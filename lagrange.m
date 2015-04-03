function result = Lagrange(degree, num_var, num_term, samples, nomials)
 
    result = LagrangeBasis(degree, num_var, num_term, samples, nomials);

    if(iscell(result))
        lagrangeBasis = result{1};
        detVandermonde = result{2};
        printf('%d ', detVandermonde);
        result = lagrangeBasis;
    else
        printf('singular');
    end
end

function lagrange_basis = LagrangeBasis(degree, num_var, num_term, sample_points, nomial_matrix)
    % Input: A polynomial with deg = d, #vars = n, #terms = m = (d+n)!/d!n!, and a vector of m sample points
    % Output: A (m+1) x m matrix that gives the Lagrange representation of the polynomial

    if(num_var ~= size(sample_points, 2))
        error('Each sample needs %d coordinates.', num_var);
    end
    if(num_term ~= size(sample_points, 1))
        sample_points
        error('Input polynomial needs %d sample points, but input has only %d samples.', num_term, size(sample_points, 1));
    end    
    
    % list all nomials of a polynomial with degree <=2
    base_matrix = zeros(num_term, num_term);
    for i = 1:num_term
        for j = 1:num_term
            base_matrix(i,j) = poly_eval([1 nomial_matrix(j, :)], sample_points(i, :));
        end
    end    
    % Note: we assume the sample points are integers
    detVandermonde = round(det(base_matrix));
    %printf('det(Vandermonde) = %d\n', d);
    if(detVandermonde==0)
        lagrange_basis = [];
        return
    end    
    
    coeff_matrix = zeros(num_term, num_term);
    for row = 1:num_term
        A = base_matrix;
        A(row, :) = [];
        for col = 1:num_term
            B = A;
            B(:, col) = [];   % B is the co-matrix of A at (row,col)
            _sign = 1 - 2*mod(row+col, 2);
            coeff_matrix(row, col) = det(B)*(_sign);
        end
    end
    lagrange_basis = {coeff_matrix, detVandermonde}; 
end

function lagrange_polynomial = LagrangePolynomial(target_polynomial, sample_points, nomial_matrix)
    % Input: A polynomial with deg = d, #vars = n, #terms = m = (d+n)!/d!n!, and a vector of m sample points
    % Output: A (m+1) x m matrix that gives the Lagrange representation of the target polynomial
    
    degree = max(sum(target_polynomial(:,2:end), 2));
    num_var = size(target_polynomial, 2) - 1;    
    num_term = prod(degree+1:degree+num_var)/factorial(num_var);
    
    if(num_var ~= size(sample_points, 2))
        error('Each sample needs %d coordinates.', num_var);
    end
    if(num_term ~= size(sample_points, 1))
        sample_points
        error('Input polynomial needs %d sample points, but input has only %d samples.', num_term, size(sample_points, 1));
    end    
    
    base_matrix = zeros(num_term, num_term);
    for i = 1:num_term
        for j = 1:num_term
            base_matrix(i,j) = poly_eval([1 nomial_matrix(j, :)], sample_points(i, :));
        end
    end    
    detVandermonde = det(base_matrix);
    if(detVandermonde==0)
        lagrange_polynomial = [];
        return
    end    
    
    coeff_matrix = zeros(num_term, num_term);
    sample_values = zeros(1, num_term);
    for row = 1:num_term
        A = base_matrix;
        A(row, :) = [];
        sample_values(1, row) = poly_eval(target_polynomial, sample_points(row, :));
        for col = 1:num_term
            B = A;
            B(:, col) = [];   % B is the co-matrix of A at (row,col)
            _sign = 1 - 2*mod(row+col, 2);
            coeff_matrix(row, col) = det(B)*(_sign);
        end
    end
    lagrange_polynomial = {(sample_values*coeff_matrix/detVandermonde)' nomial_matrix};
end

function val = poly_eval(polynomial, point)
    val = 0;
    num_term = size(polynomial, 1);
    for k = 1:num_term
         val = val + polynomial(k, 1) * prod(point .^ polynomial(k, 2:end));
    end
end

if(nargin < 1)
    error('Error %d : %s needs a matrix of sample points as input.', nargin, program_name());
end

function serialize(matrix)
    w = size(matrix, 1);
    h = size(matrix, 2);
    for i = 1:w
        for j = 1:h
            printf('%.5f ', matrix(i,j));
        end
    end
end

%Lagrange(eval(argv(){1}))
args = argv();
serialize(Lagrange(eval(args{1}), eval(args{2}),eval(args{3}), eval(args{4}), eval(args{5})))
