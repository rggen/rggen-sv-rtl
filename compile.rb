['apb', 'axi4lite', 'wishbone'].each do |protocol|
  file_list "compile_#{protocol}.rb", from: :current
end
