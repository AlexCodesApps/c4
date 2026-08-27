How Does Variance Work?
```
forall a.
	*a :> *mut a -- covariant
	mut *a :> mut *mut a; -- covariant
	mut a <> a
	*fun(*mut a) :> *fun(*a)
    *a :> &a -- covariant
    *fun(&a) :> *fun(*a) -- contravariant
    *fun(&mut &a) :> *fun(&mut *a) -- invariant
```
