use std::rc::Rc; fn main() { let y1 = Rc::new("y".to_string()); let y2 = y1.clone(); println!("ptr_eq={} content_eq={}", Rc::ptr_eq(&y1, &y2), *y1==*y2); }
