/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Constructions

/-!
# Type-tag transport for continuous monoid homomorphisms and equivalences

`Multiplicative` and `Additive` carry the topology of their underlying type via
`Mathlib.Topology.Constructions`, with `continuous_ofAdd`, `continuous_toAdd`, `continuous_ofMul`,
and `continuous_toMul`. This file upgrades Mathlib's algebraic type-tag maps on `AddMonoidHom`,
`MonoidHom`, `AddEquiv`, and `MulEquiv` to `ContinuousAddMonoidHom`, `ContinuousMonoidHom`,
`ContinuousAddEquiv`, and `ContinuousMulEquiv`, including the binary and dependent product
isomorphisms `ContinuousMulEquiv.prodMultiplicative`, `ContinuousAddEquiv.prodAdditive`,
`ContinuousMulEquiv.piMultiplicative`, and `ContinuousAddEquiv.piAdditive`.
-/

public section

section Hom

variable {A B M N : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace M] [TopologicalSpace N]

/-- Reinterpret a continuous additive homomorphism `A →ₜ+ B` as a continuous multiplicative
homomorphism `Multiplicative A →ₜ* Multiplicative B`. -/
@[expose] def ContinuousAddMonoidHom.toMultiplicative [AddMonoid A] [AddMonoid B] (φ : A →ₜ+ B) :
    Multiplicative A →ₜ* Multiplicative B where
  toMonoidHom := φ.toAddMonoidHom.toMultiplicative
  continuous_toFun := continuous_ofAdd.comp (φ.continuous.comp continuous_toAdd)

@[simp] theorem ContinuousAddMonoidHom.toMultiplicative_apply [AddMonoid A] [AddMonoid B]
    (φ : A →ₜ+ B) (x : Multiplicative A) :
    φ.toMultiplicative x = Multiplicative.ofAdd (φ x.toAdd) := (rfl)

/-- Reinterpret a continuous multiplicative homomorphism `M →ₜ* N` as a continuous additive
homomorphism `Additive M →ₜ+ Additive N`. -/
@[expose] def ContinuousMonoidHom.toAdditive [Monoid M] [Monoid N] (φ : M →ₜ* N) :
    Additive M →ₜ+ Additive N where
  toAddMonoidHom := φ.toMonoidHom.toAdditive
  continuous_toFun := continuous_ofMul.comp (φ.continuous.comp continuous_toMul)

@[simp] theorem ContinuousMonoidHom.toAdditive_apply [Monoid M] [Monoid N]
    (φ : M →ₜ* N) (x : Additive M) :
    φ.toAdditive x = Additive.ofMul (φ x.toMul) := (rfl)

/-- Reinterpret a continuous additive equivalence `A ≃ₜ+ B` as a continuous multiplicative
equivalence `Multiplicative A ≃ₜ* Multiplicative B`. -/
@[expose] def ContinuousAddEquiv.toMultiplicative [Add A] [Add B] (e : A ≃ₜ+ B) :
    Multiplicative A ≃ₜ* Multiplicative B where
  toMulEquiv := AddEquiv.toMultiplicative e.toAddEquiv
  continuous_toFun := continuous_ofAdd.comp (e.continuous.comp continuous_toAdd)
  continuous_invFun := continuous_ofAdd.comp (e.continuous_invFun.comp continuous_toAdd)

@[simp] theorem ContinuousAddEquiv.toMultiplicative_apply [Add A] [Add B]
    (e : A ≃ₜ+ B) (x : Multiplicative A) :
    e.toMultiplicative x = Multiplicative.ofAdd (e x.toAdd) := (rfl)

@[simp] theorem ContinuousAddEquiv.toMultiplicative_symm [Add A] [Add B] (e : A ≃ₜ+ B) :
    e.toMultiplicative.symm = e.symm.toMultiplicative := (rfl)

/-- Reinterpret a continuous multiplicative equivalence `M ≃ₜ* N` as a continuous additive
equivalence `Additive M ≃ₜ+ Additive N`. -/
@[expose] def ContinuousMulEquiv.toAdditive [Mul M] [Mul N] (e : M ≃ₜ* N) :
    Additive M ≃ₜ+ Additive N where
  toAddEquiv := MulEquiv.toAdditive e.toMulEquiv
  continuous_toFun := continuous_ofMul.comp (e.continuous.comp continuous_toMul)
  continuous_invFun := continuous_ofMul.comp (e.continuous_invFun.comp continuous_toMul)

@[simp] theorem ContinuousMulEquiv.toAdditive_apply [Mul M] [Mul N]
    (e : M ≃ₜ* N) (x : Additive M) :
    e.toAdditive x = Additive.ofMul (e x.toMul) := (rfl)

@[simp] theorem ContinuousMulEquiv.toAdditive_symm [Mul M] [Mul N] (e : M ≃ₜ* N) :
    e.toAdditive.symm = e.symm.toAdditive := (rfl)

end Hom

section PiProd

variable {ι : Type*}

section PiMul
variable (K : ι → Type*) [∀ i, Add (K i)] [∀ i, TopologicalSpace (K i)]

/-- `Multiplicative (∀ i, K i)` is continuously multiplicatively equivalent to
`∀ i, Multiplicative (K i)`. -/
@[expose] def ContinuousMulEquiv.piMultiplicative :
    Multiplicative (∀ i, K i) ≃ₜ* ∀ i, Multiplicative (K i) where
  toMulEquiv := MulEquiv.piMultiplicative K
  continuous_toFun := continuous_pi fun i =>
    continuous_ofAdd.comp ((continuous_apply i).comp continuous_toAdd)
  continuous_invFun := continuous_ofAdd.comp <| continuous_pi fun i =>
    continuous_toAdd.comp (continuous_apply i)

@[simp] theorem ContinuousMulEquiv.piMultiplicative_apply
    (x : Multiplicative (∀ i, K i)) (i : ι) :
    ContinuousMulEquiv.piMultiplicative K x i = Multiplicative.ofAdd (x.toAdd i) := (rfl)

@[simp] theorem ContinuousMulEquiv.piMultiplicative_symm_apply
    (x : ∀ i, Multiplicative (K i)) :
    (ContinuousMulEquiv.piMultiplicative K).symm x =
      Multiplicative.ofAdd fun i => (x i).toAdd := (rfl)
end PiMul

section PiAdd
variable (K : ι → Type*) [∀ i, Mul (K i)] [∀ i, TopologicalSpace (K i)]

/-- `Additive (∀ i, K i)` is continuously additively equivalent to `∀ i, Additive (K i)`. -/
@[expose] def ContinuousAddEquiv.piAdditive : Additive (∀ i, K i) ≃ₜ+ ∀ i, Additive (K i) where
  toAddEquiv := AddEquiv.piAdditive K
  continuous_toFun := continuous_pi fun i =>
    continuous_ofMul.comp ((continuous_apply i).comp continuous_toMul)
  continuous_invFun := continuous_ofMul.comp <| continuous_pi fun i =>
    continuous_toMul.comp (continuous_apply i)

@[simp] theorem ContinuousAddEquiv.piAdditive_apply (x : Additive (∀ i, K i)) (i : ι) :
    ContinuousAddEquiv.piAdditive K x i = Additive.ofMul (x.toMul i) := (rfl)

@[simp] theorem ContinuousAddEquiv.piAdditive_symm_apply (x : ∀ i, Additive (K i)) :
    (ContinuousAddEquiv.piAdditive K).symm x = Additive.ofMul fun i => (x i).toMul := (rfl)
end PiAdd

section ProdMul
variable (G H : Type*) [Add G] [Add H] [TopologicalSpace G] [TopologicalSpace H]

/-- `Multiplicative (G × H)` is continuously multiplicatively equivalent to
`Multiplicative G × Multiplicative H`. -/
@[expose] def ContinuousMulEquiv.prodMultiplicative :
    Multiplicative (G × H) ≃ₜ* Multiplicative G × Multiplicative H where
  toMulEquiv := MulEquiv.prodMultiplicative G H
  continuous_toFun := (continuous_ofAdd.comp (continuous_fst.comp continuous_toAdd)).prodMk
    (continuous_ofAdd.comp (continuous_snd.comp continuous_toAdd))
  continuous_invFun := continuous_ofAdd.comp
    ((continuous_toAdd.comp continuous_fst).prodMk (continuous_toAdd.comp continuous_snd))

@[simp] theorem ContinuousMulEquiv.prodMultiplicative_apply (x : Multiplicative (G × H)) :
    ContinuousMulEquiv.prodMultiplicative G H x =
      (Multiplicative.ofAdd x.toAdd.1, Multiplicative.ofAdd x.toAdd.2) := (rfl)

@[simp] theorem ContinuousMulEquiv.prodMultiplicative_symm_apply
    (x : Multiplicative G × Multiplicative H) :
    (ContinuousMulEquiv.prodMultiplicative G H).symm x =
      Multiplicative.ofAdd (x.1.toAdd, x.2.toAdd) := (rfl)
end ProdMul

section ProdAdd
variable (G H : Type*) [Mul G] [Mul H] [TopologicalSpace G] [TopologicalSpace H]

/-- `Additive (G × H)` is continuously additively equivalent to `Additive G × Additive H`. -/
@[expose] def ContinuousAddEquiv.prodAdditive : Additive (G × H) ≃ₜ+ Additive G × Additive H where
  toAddEquiv := AddEquiv.prodAdditive G H
  continuous_toFun := (continuous_ofMul.comp (continuous_fst.comp continuous_toMul)).prodMk
    (continuous_ofMul.comp (continuous_snd.comp continuous_toMul))
  continuous_invFun := continuous_ofMul.comp
    ((continuous_toMul.comp continuous_fst).prodMk (continuous_toMul.comp continuous_snd))

@[simp] theorem ContinuousAddEquiv.prodAdditive_apply (x : Additive (G × H)) :
    ContinuousAddEquiv.prodAdditive G H x =
      (Additive.ofMul x.toMul.1, Additive.ofMul x.toMul.2) := (rfl)

@[simp] theorem ContinuousAddEquiv.prodAdditive_symm_apply (x : Additive G × Additive H) :
    (ContinuousAddEquiv.prodAdditive G H).symm x =
      Additive.ofMul (x.1.toMul, x.2.toMul) := (rfl)
end ProdAdd

end PiProd
