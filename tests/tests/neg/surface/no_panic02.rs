trait MyTrait {
    #[flux_rs::no_panic]
    fn f1(&self) -> usize;
}


struct MyStruct {}

impl MyTrait for MyStruct {
    fn f1(&self) -> usize { // ~ ERROR may panic
        1
    }
}