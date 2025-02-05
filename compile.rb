['apb', 'axi4lite', 'avalon', 'wishbone', 'native'].each do |protocol|
  file_list "compile_#{protocol}.rb", from: :current
end
