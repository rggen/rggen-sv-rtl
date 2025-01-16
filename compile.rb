['apb', 'axi4lite', 'wishbone', 'native'].each do |protocol|
  file_list "compile_#{protocol}.rb", from: :current
end
