/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.TensorProduct.Pi
public import TauCeti.Algebra.TensorProduct.BaseChange
public import TauCeti.RingTheory.Unramified.Frame.Basic

/-!
# Slot projections and the universal frame of a frame algebra

Let `S` be an essentially finite type, formally unramified `R`-algebra and `ι` a finite type, and
let `P = TauCeti.Algebra.FrameAlgebra R S ι` be the frame algebra of `ι`-tuples of pairwise
distinct points of `Spec S`.

The `i`-th tensor factor inclusion `S → ⨂[R] _ : ι, S` followed by the quotient map gives the
`i`-th *slot projection* `TauCeti.Algebra.FrameAlgebra.slotAlgHom R S i : S →ₐ[R] P`. Together they
form the universal `ι`-tuple of pairwise distinct `P`-points of `S`: distinct slots annihilate the
diagonal idempotent (`TauCeti.Algebra.FrameAlgebra.productMap_slotAlgHom_elem`), and every
`ι`-tuple of `T`-points of `S` separating distinct slots factors uniquely through `P`
(`TauCeti.Algebra.FrameAlgebra.liftPi`).

Extending the `ι` slot projections `P`-linearly defines the *universal frame*

  `TauCeti.Algebra.FrameAlgebra.universalFrame R S ι : P ⊗[R] S →ₐ[P] (ι → P)`,
  `p ⊗ s ↦ (p * slotAlgHom R S i s)_i`.

For the split algebra `S = ι → R`, read through `P ≃ (Equiv.Perm ι → R)`, the universal frame is
the coordinate twist `g ↦ (i, τ) ↦ g (τ i) τ`, hence an isomorphism
(`TauCeti.Algebra.FrameAlgebra.bijective_universalFrame_pi`). Forming `universalFrame` commutes
with base change (`TauCeti.Algebra.FrameAlgebra.universalFrame_baseChange`) and with algebra
isomorphisms (`TauCeti.Algebra.FrameAlgebra.universalFrame_congr`), so bijectivity of
`universalFrame` descends along any faithfully flat extension `R → T` splitting `S` as `ι → T`
(`TauCeti.Algebra.FrameAlgebra.bijective_universalFrame_of_algEquiv_pi`). Over its frame algebra,
any locally split algebra of rank `|ι|` therefore becomes isomorphic to `ι → P`.

## Main definitions

* `TauCeti.Algebra.FrameAlgebra.slotAlgHom R S i`: the `i`-th canonical `R`-algebra map
  `S →ₐ[R] FrameAlgebra R S ι`.
* `TauCeti.Algebra.FrameAlgebra.liftPi`: the universal property of `FrameAlgebra` for `ι`-tuples
  of `R`-algebra maps `S →ₐ[R] T` separating distinct slots.
* `TauCeti.Algebra.FrameAlgebra.universalFrame R S ι`: the canonical `P`-algebra map
  `FrameAlgebra R S ι ⊗[R] S →ₐ[FrameAlgebra R S ι] (ι → FrameAlgebra R S ι)`.
* `TauCeti.Algebra.FrameAlgebra.universalFrameEquivPi`: the universal frame as an algebra
  isomorphism for the split algebra `ι → R`.
* `TauCeti.Algebra.FrameAlgebra.universalFrameEquivOfAlgEquivPi`: the universal frame as an algebra
  isomorphism when `T ⊗[R] S ≃ₐ[T] (ι → T)` for a faithfully flat `R`-algebra `T`.

## Main results

* `TauCeti.Algebra.FrameAlgebra.productMap_slotAlgHom_elem`: distinct slot maps annihilate the
  diagonal idempotent `Algebra.FormallyUnramified.elem R S`.
* `TauCeti.Algebra.FrameAlgebra.slotAlgHom_injective`: over a nontrivial frame algebra, distinct
  indices give distinct slot maps.
* `TauCeti.Algebra.FrameAlgebra.bijective_universalFrame_baseChange_iff`: bijectivity of
  `universalFrame` descends along faithfully flat base change.
* `TauCeti.Algebra.FrameAlgebra.bijective_universalFrame_pi`: `universalFrame R (ι → R) ι` is
  bijective.
* `TauCeti.Algebra.FrameAlgebra.bijective_universalFrame_of_algEquiv_pi`: `universalFrame R S ι`
  is bijective whenever `S` becomes isomorphic to `ι → T` after a faithfully flat extension.

## References

* [Stacks Project, Tag 0BN2](https://stacks.math.columbia.edu/tag/0BN2).
* P. Scholze, *Étale cohomology of diamonds*, proof of Lemma 15.3.
-/

public section

open scoped TensorProduct

namespace TauCeti.Algebra.FrameAlgebra

open PiTensorProduct

section Slot

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `i`-th canonical slot map `S →ₐ[R] FrameAlgebra R S ι`, sending `s` to the class of `s`
placed in the `i`-th tensor factor. Geometrically, the `ι` slot maps are the projections from the
frame scheme of `ι`-tuples of pairwise distinct points of `Spec S` to `Spec S`. -/
noncomputable def slotAlgHom (i : ι) : S →ₐ[R] FrameAlgebra R S ι :=
  (Ideal.Quotient.mkₐ R (Ideal.span {1 - distinctIdempotent R S ι})).comp
    (singleAlgHom (R := R) (A := fun _ : ι ↦ S) i)

variable {R S}

/-- `TauCeti.Algebra.FrameAlgebra.slotAlgHom` sends `s` to the quotient class of `singleAlgHom i s`
in the frame algebra. -/
theorem slotAlgHom_apply (i : ι) (s : S) :
    slotAlgHom R S i s =
      Ideal.Quotient.mk (Ideal.span {1 - distinctIdempotent R S ι})
        (singleAlgHom (R := R) (A := fun _ : ι ↦ S) i s) :=
  (rfl)

/-- Two `R`-algebra maps out of the frame algebra are equal when they agree on every slot. -/
theorem algHom_ext {T : Type*} [Semiring T] [Algebra R T]
    {f g : FrameAlgebra R S ι →ₐ[R] T}
    (h : ∀ i, f.comp (slotAlgHom R S i) = g.comp (slotAlgHom R S i)) : f = g :=
  Ideal.Quotient.algHom_ext R <| PiTensorProduct.algHom_ext fun i ↦ by
    simpa only [slotAlgHom, AlgHom.comp_assoc] using h i

/-- A permutation `σ` of the slots sends `slotAlgHom R S i s` to `slotAlgHom R S (σ i) s`. -/
@[simp]
theorem permAlgEquiv_slotAlgHom (σ : Equiv.Perm ι) (i : ι) (s : S) :
    permAlgEquiv R S ι σ (slotAlgHom R S i s) = slotAlgHom R S (σ i) s := by
  rw [slotAlgHom_apply, ← smul_def, smul_mk, permAlgEquiv_singleAlgHom, ← slotAlgHom_apply]

/-- Scalar multiplication by `σ : Equiv.Perm ι` moves slot `i` to slot `σ i`. -/
@[simp]
theorem smul_slotAlgHom (σ : Equiv.Perm ι) (i : ι) (s : S) :
    σ • slotAlgHom R S i s = slotAlgHom R S (σ i) s :=
  permAlgEquiv_slotAlgHom σ i s

/-- Distinct slot maps separate points: their product map kills the diagonal idempotent
`Algebra.FormallyUnramified.elem R S`. -/
@[simp]
theorem productMap_slotAlgHom_elem {i j : ι} (hij : i ≠ j) :
    Algebra.TensorProduct.productMap (slotAlgHom R S i) (slotAlgHom R S j)
        (Algebra.FormallyUnramified.elem R S) = 0 := by
  have h := map_tensorPowDiagonal
    (Ideal.Quotient.mkₐ R (Ideal.span {1 - distinctIdempotent R S ι})) i j
  rw [Ideal.Quotient.mkₐ_eq_mk, mk_tensorPowDiagonal hij] at h
  exact h.symm

/-- When the frame algebra is nontrivial, distinct indices yield distinct slot maps
`S →ₐ[R] FrameAlgebra R S ι`. -/
theorem slotAlgHom_injective [Nontrivial (FrameAlgebra R S ι)] :
    Function.Injective (slotAlgHom R S : ι → (S →ₐ[R] FrameAlgebra R S ι)) := by
  intro i j hij
  by_contra hne
  have h0 := productMap_slotAlgHom_elem (R := R) (S := S) hne
  rw [hij] at h0
  have hmul : Algebra.TensorProduct.productMap (slotAlgHom R S j) (slotAlgHom R S j) =
      (slotAlgHom R S j).comp (Algebra.TensorProduct.lmul' R) :=
    Algebra.TensorProduct.ext' fun a b ↦ by simp [map_mul]
  rw [hmul, AlgHom.comp_apply, Algebra.FormallyUnramified.lmul_elem, map_one] at h0
  exact one_ne_zero h0

section LiftPi

variable {T : Type*} [CommSemiring T] [Algebra R T]

/-- Universal property of the frame algebra in terms of slot maps: an `ι`-tuple of `R`-algebra
maps `f : ι → (S →ₐ[R] T)` whose distinct pairs annihilate the diagonal idempotent factors
through a unique `R`-algebra map `FrameAlgebra R S ι →ₐ[R] T`. -/
noncomputable def liftPi (f : ι → (S →ₐ[R] T))
    (hf : ∀ i j, i ≠ j →
      Algebra.TensorProduct.productMap (f i) (f j) (Algebra.FormallyUnramified.elem R S) = 0) :
    FrameAlgebra R S ι →ₐ[R] T :=
  lift (PiTensorProduct.productMap f) fun i j hij ↦ by
    have hcomp (k : ι) : (PiTensorProduct.productMap f).comp (singleAlgHom k) = f k :=
      AlgHom.ext (productMap_singleAlgHom f k)
    rw [map_tensorPowDiagonal, hcomp i, hcomp j, hf i j hij]

/-- `TauCeti.Algebra.FrameAlgebra.liftPi` restricts to `f i` on the `i`-th slot. -/
@[simp]
theorem liftPi_slotAlgHom (f : ι → (S →ₐ[R] T))
    (hf : ∀ i j, i ≠ j →
      Algebra.TensorProduct.productMap (f i) (f j) (Algebra.FormallyUnramified.elem R S) = 0)
    (i : ι) (s : S) :
    liftPi f hf (slotAlgHom R S i s) = f i s := by
  simp [liftPi, slotAlgHom_apply, -singleAlgHom_apply]

/-- Composing `TauCeti.Algebra.FrameAlgebra.liftPi` with the `i`-th slot map recovers `f i`. -/
@[simp]
theorem liftPi_comp_slotAlgHom (f : ι → (S →ₐ[R] T))
    (hf : ∀ i j, i ≠ j →
      Algebra.TensorProduct.productMap (f i) (f j) (Algebra.FormallyUnramified.elem R S) = 0)
    (i : ι) :
    (liftPi f hf).comp (slotAlgHom R S i) = f i :=
  AlgHom.ext (liftPi_slotAlgHom f hf i)

/-- An `R`-algebra map out of the frame algebra equals `liftPi f hf` if and only if its
restriction to slot `i` is `f i` for every `i`. -/
theorem eq_liftPi_iff (f : ι → (S →ₐ[R] T))
    (hf : ∀ i j, i ≠ j →
      Algebra.TensorProduct.productMap (f i) (f j) (Algebra.FormallyUnramified.elem R S) = 0)
    (ψ : FrameAlgebra R S ι →ₐ[R] T) :
    ψ = liftPi f hf ↔ ∀ i, ψ.comp (slotAlgHom R S i) = f i :=
  ⟨fun h i ↦ h ▸ liftPi_comp_slotAlgHom f hf i,
    fun h ↦ algHom_ext fun i ↦ (h i).trans (liftPi_comp_slotAlgHom f hf i).symm⟩

end LiftPi

/-- Base change of the frame algebra carries `t ⊗ slotAlgHom R S i s` to
`slotAlgHom T (T ⊗[R] S) i (t ⊗ s)`. -/
@[simp]
theorem baseChangeEquiv_tmul_slotAlgHom {T : Type*} [CommRing T] [Algebra R T]
    (t : T) (i : ι) (s : S) :
    baseChangeEquiv R S T ι (t ⊗ₜ slotAlgHom R S i s) =
      slotAlgHom T (T ⊗[R] S) i (t ⊗ₜ s) := by
  apply (baseChangeEquiv R S T ι).symm.injective
  rw [AlgEquiv.symm_apply_apply]
  have h1 : baseChangeEquiv R S T ι (1 ⊗ₜ slotAlgHom R S i s) =
      slotAlgHom T (T ⊗[R] S) i (1 ⊗ₜ s) := by
    rw [slotAlgHom_apply, baseChangeEquiv_tmul_mk, baseChangeAlgEquiv_one_tmul_singleAlgHom,
      ← slotAlgHom_apply]
  have ht : slotAlgHom T (T ⊗[R] S) i (t ⊗ₜ s) = t • slotAlgHom T (T ⊗[R] S) i (1 ⊗ₜ s) := by
    rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [ht, ← h1, map_smul, AlgEquiv.symm_apply_apply, TensorProduct.smul_tmul', smul_eq_mul,
    mul_one]

/-- `TauCeti.Algebra.FrameAlgebra.congr e` carries `slotAlgHom R S i s` to
`slotAlgHom R S' i (e s)`. -/
@[simp]
theorem congr_slotAlgHom {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra.EssFiniteType R S']
    [Algebra.FormallyUnramified R S'] (e : S ≃ₐ[R] S') (i : ι) (s : S) :
    congr ι e (slotAlgHom R S i s) = slotAlgHom R S' i (e s) := by
  rw [slotAlgHom_apply, congr_mk, congrAlgEquiv_singleAlgHom, ← slotAlgHom_apply]

/-- `TauCeti.Algebra.FrameAlgebra.congr` of the identity equivalence is the identity. -/
@[simp]
theorem congr_refl : congr ι (AlgEquiv.refl : S ≃ₐ[R] S) = AlgEquiv.refl :=
  AlgEquiv.coe_toAlgHom_injective <| algHom_ext fun i ↦ AlgHom.ext fun s ↦ by simp

/-- `TauCeti.Algebra.FrameAlgebra.congr` commutes with composition of algebra equivalences. -/
theorem congr_trans {S' S'' : Type*} [CommRing S'] [Algebra R S'] [Algebra.EssFiniteType R S']
    [Algebra.FormallyUnramified R S'] [CommRing S''] [Algebra R S''] [Algebra.EssFiniteType R S'']
    [Algebra.FormallyUnramified R S''] (e₁ : S ≃ₐ[R] S') (e₂ : S' ≃ₐ[R] S'') :
    congr ι (e₁.trans e₂) = (congr ι e₁).trans (congr ι e₂) :=
  AlgEquiv.coe_toAlgHom_injective <| algHom_ext fun i ↦ AlgHom.ext fun s ↦ by simp

/-- The inverse of `TauCeti.Algebra.FrameAlgebra.congr e` is `congr ι e.symm`. -/
@[simp]
theorem congr_symm {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra.EssFiniteType R S']
    [Algebra.FormallyUnramified R S'] (e : S ≃ₐ[R] S') :
    (congr ι e).symm = congr ι e.symm := by
  apply AlgEquiv.ext
  intro y
  apply (congr ι e).injective
  rw [AlgEquiv.apply_symm_apply, ← AlgEquiv.trans_apply, ← congr_trans, AlgEquiv.symm_trans_self,
    congr_refl]
  rfl

/-- On the split algebra `κ → R`, `TauCeti.Algebra.FrameAlgebra.piEquiv` evaluates `slotAlgHom` at
an embedding `e : ι ↪ κ` by evaluating at `e i`. -/
@[simp]
theorem piEquiv_slotAlgHom {κ : Type*} [Finite κ] (i : ι) (f : κ → R) (e : ι ↪ κ) :
    piEquiv R ι κ (slotAlgHom R (κ → R) i f) e = f (e i) := by
  rw [slotAlgHom_apply, piEquiv_mk, piScalarAlgEquiv_singleAlgHom]

/-- On the split algebra `ι → R`, `TauCeti.Algebra.FrameAlgebra.permEquiv` evaluates `slotAlgHom`
at a permutation `τ : Equiv.Perm ι` by evaluating at `τ i`. -/
@[simp]
theorem permEquiv_slotAlgHom (i : ι) (f : ι → R) (τ : Equiv.Perm ι) :
    permEquiv R ι (slotAlgHom R (ι → R) i f) τ = f (τ i) := by
  rw [permEquiv_apply, piEquiv_slotAlgHom, Equiv.coe_toEmbedding]

end Slot

section UniversalFrame

variable (R S ι : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
  [Fintype ι] [DecidableEq ι]

/-- The *universal frame* of `S` over `FrameAlgebra R S ι`: the `FrameAlgebra R S ι`-algebra map
`FrameAlgebra R S ι ⊗[R] S →ₐ[FrameAlgebra R S ι] (ι → FrameAlgebra R S ι)` sending `p ⊗ s` to
`(p * slotAlgHom R S i s)_i`. Geometrically, base-changing `Spec S → Spec R` to the frame scheme
produces `|ι|` canonical tautological sections, which trivialize `Spec S` when `S` is locally split
of rank `|ι|`. -/
noncomputable def universalFrame :
    FrameAlgebra R S ι ⊗[R] S →ₐ[FrameAlgebra R S ι] (ι → FrameAlgebra R S ι) :=
  AlgHom.pi fun i ↦ Algebra.TensorProduct.lift (AlgHom.id _ _) (slotAlgHom R S i)
    fun _ _ ↦ Commute.all _ _

variable {R S ι}

/-- `TauCeti.Algebra.FrameAlgebra.universalFrame` sends `p ⊗ s` at coordinate `i` to
`p * slotAlgHom R S i s`. -/
@[simp]
theorem universalFrame_tmul (p : FrameAlgebra R S ι) (s : S) (i : ι) :
    universalFrame R S ι (p ⊗ₜ s) i = p * slotAlgHom R S i s :=
  (rfl)

/-- `TauCeti.Algebra.FrameAlgebra.universalFrame` intertwines the action of `σ : Equiv.Perm ι` on
the frame algebra factor with the semilinear permutation `g ↦ (j ↦ σ • g (σ⁻¹ j))` of the
`ι`-indexed product. -/
theorem universalFrame_map_permAlgEquiv (σ : Equiv.Perm ι) (z : FrameAlgebra R S ι ⊗[R] S)
    (j : ι) :
    universalFrame R S ι
        (Algebra.TensorProduct.map (permAlgEquiv R S ι σ).toAlgHom (AlgHom.id R S) z) j =
      σ • universalFrame R S ι z (σ.symm j) := by
  induction z using TensorProduct.inductionOn with
  | tmul p s =>
    simp [← smul_def, smul_mul']
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy, smul_def]

/-- `TauCeti.Algebra.FrameAlgebra.universalFrame` commutes with algebra isomorphisms
`e : S ≃ₐ[R] S'` via `FrameAlgebra.congr ι e`. -/
theorem universalFrame_congr {S' : Type*} [CommRing S'] [Algebra R S']
    [Algebra.EssFiniteType R S'] [Algebra.FormallyUnramified R S'] (e : S ≃ₐ[R] S')
    (z : FrameAlgebra R S ι ⊗[R] S) (i : ι) :
    universalFrame R S' ι (Algebra.TensorProduct.congr (congr ι e) e z) i =
      congr ι e (universalFrame R S ι z i) := by
  induction z using TensorProduct.inductionOn with
  | tmul p s => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- Bijectivity of `TauCeti.Algebra.FrameAlgebra.universalFrame` is invariant under `R`-algebra
isomorphisms of `S`. -/
theorem bijective_universalFrame_congr_iff {S' : Type*} [CommRing S'] [Algebra R S']
    [Algebra.EssFiniteType R S'] [Algebra.FormallyUnramified R S'] (e : S ≃ₐ[R] S') :
    Function.Bijective (universalFrame R S' ι) ↔ Function.Bijective (universalFrame R S ι) := by
  let c₁ := Algebra.TensorProduct.congr (congr ι e) e
  let c₂ : (ι → FrameAlgebra R S ι) ≃ₐ[R] (ι → FrameAlgebra R S' ι) :=
    AlgEquiv.piCongrRight fun _ ↦ congr ι e
  have hcomp : ⇑(universalFrame R S' ι) ∘ ⇑c₁ = ⇑c₂ ∘ ⇑(universalFrame R S ι) := by
    funext z
    ext i
    exact universalFrame_congr e z i
  rw [← Function.Bijective.of_comp_iff _ c₁.bijective, hcomp,
    Function.Bijective.of_comp_iff' c₂.bijective]

/-- `TauCeti.Algebra.FrameAlgebra.universalFrame` commutes with base change along `R → T`: read
through `T ⊗[R] (P ⊗[R] S) ≃ (T ⊗[R] P) ⊗[T] (T ⊗[R] S)` and `baseChangeEquiv`, the universal
frame of `T ⊗[R] S` over `T` is `id ⊗ universalFrame R S ι` followed by `piRight` and
`baseChangeEquiv` in each coordinate. -/
theorem universalFrame_baseChange (T : Type*) [CommRing T] [Algebra R T]
    (z : T ⊗[R] (FrameAlgebra R S ι ⊗[R] S)) (i : ι) :
    universalFrame T (T ⊗[R] S) ι
        (Algebra.TensorProduct.congr (baseChangeEquiv R S T ι)
          (AlgEquiv.refl : T ⊗[R] S ≃ₐ[T] T ⊗[R] S)
          (TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv R T (FrameAlgebra R S ι) S z))
        i =
      baseChangeEquiv R S T ι
        (Algebra.TensorProduct.piRight R T T (fun _ : ι ↦ FrameAlgebra R S ι)
          ((((universalFrame R S ι).restrictScalars R).toLinearMap.lTensor T) z) i) := by
  let γ : FrameAlgebra R S ι ⊗[R] S →ₗ[R] (ι → FrameAlgebra R S ι) :=
    ((universalFrame R S ι).restrictScalars R).toLinearMap
  let e := (TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv R T (FrameAlgebra R S ι)
    S).trans (Algebra.TensorProduct.congr (baseChangeEquiv R S T ι)
      (AlgEquiv.refl : T ⊗[R] S ≃ₐ[T] T ⊗[R] S))
  let π := (Algebra.TensorProduct.piRight R T T fun _ : ι ↦ FrameAlgebra R S ι).trans
    (AlgEquiv.piCongrRight fun _ ↦ baseChangeEquiv R S T ι)
  let lhs : T ⊗[R] (FrameAlgebra R S ι ⊗[R] S) →ₗ[R] (ι → FrameAlgebra T (T ⊗[R] S) ι) :=
    ((universalFrame T (T ⊗[R] S) ι).restrictScalars R).toLinearMap.comp
      (e.toLinearEquiv.restrictScalars R).toLinearMap
  let rhs : T ⊗[R] (FrameAlgebra R S ι ⊗[R] S) →ₗ[R] (ι → FrameAlgebra T (T ⊗[R] S) ι) :=
    (π.toLinearEquiv.restrictScalars R).toLinearMap.comp (γ.lTensor T)
  suffices h : lhs = rhs from congrFun (DFunLike.congr_fun h z) i
  refine TensorProduct.ext_threefold' fun t p s ↦ ?_
  ext j
  simp only [lhs, rhs, e, π, γ, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.restrictScalars_apply, AlgEquiv.toLinearEquiv_apply, AlgEquiv.trans_apply,
    AlgHom.toLinearMap_apply, AlgHom.restrictScalars_apply, LinearMap.lTensor_tmul,
    TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_refl, id_eq,
    universalFrame_tmul, Algebra.TensorProduct.piRight_tmul, AlgEquiv.piCongrRight_apply]
  rw [← baseChangeEquiv_tmul_slotAlgHom, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

/-- Bijectivity of `TauCeti.Algebra.FrameAlgebra.universalFrame` descends along a faithfully flat
base extension `R → T`. -/
theorem bijective_universalFrame_baseChange_iff (T : Type*) [CommRing T] [Algebra R T]
    [Module.FaithfullyFlat R T] :
    Function.Bijective (universalFrame T (T ⊗[R] S) ι) ↔
      Function.Bijective (universalFrame R S ι) := by
  let γ : FrameAlgebra R S ι ⊗[R] S →ₗ[R] (ι → FrameAlgebra R S ι) :=
    ((universalFrame R S ι).restrictScalars R).toLinearMap
  let e := (TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv R T (FrameAlgebra R S ι)
    S).trans (Algebra.TensorProduct.congr (baseChangeEquiv R S T ι)
      (AlgEquiv.refl : T ⊗[R] S ≃ₐ[T] T ⊗[R] S))
  let π := (Algebra.TensorProduct.piRight R T T fun _ : ι ↦ FrameAlgebra R S ι).trans
    (AlgEquiv.piCongrRight fun _ ↦ baseChangeEquiv R S T ι)
  -- Read through `e` and `π`, the universal frame for `T ⊗[R] S` is `id ⊗ γ`.
  have hcomp : ⇑(universalFrame T (T ⊗[R] S) ι) ∘ ⇑e = ⇑π ∘ ⇑(γ.lTensor T) := by
    funext z
    ext i
    exact universalFrame_baseChange T z i
  rw [← Function.Bijective.of_comp_iff _ e.bijective, hcomp,
    Function.Bijective.of_comp_iff' π.bijective,
    Module.FaithfullyFlat.lTensor_bijective_iff_bijective]
  rfl

variable (R ι)

/-- **Split model of the universal frame.** For the split algebra `ι → R`, the universal frame
`FrameAlgebra R (ι → R) ι ⊗[R] (ι → R) → (ι → FrameAlgebra R (ι → R) ι)` is bijective: read
through `permEquiv R ι`, it is the coordinate twist `g ↦ (i, τ) ↦ g (τ i) τ`, with inverse
`h ↦ (j, τ) ↦ h (τ⁻¹ j) τ`. -/
theorem bijective_universalFrame_pi :
    Function.Bijective (universalFrame R (ι → R) ι) := by
  let e₁ : FrameAlgebra R (ι → R) ι ⊗[R] (ι → R) ≃ₐ[R] (ι → Equiv.Perm ι → R) :=
    (Algebra.TensorProduct.congr (permEquiv R ι) AlgEquiv.refl).trans
      (Algebra.TensorProduct.piScalarRight R R (Equiv.Perm ι → R) ι)
  let e₂ : (ι → FrameAlgebra R (ι → R) ι) ≃ₐ[R] (ι → Equiv.Perm ι → R) :=
    AlgEquiv.piCongrRight fun _ ↦ permEquiv R ι
  let twist : (ι → Equiv.Perm ι → R) ≃ (ι → Equiv.Perm ι → R) :=
    { toFun := fun g i τ ↦ g (τ i) τ
      invFun := fun h j τ ↦ h (τ.symm j) τ
      left_inv := fun g ↦ by ext j τ; simp
      right_inv := fun h ↦ by ext i τ; simp }
  have hcomp : ⇑e₂ ∘ ⇑(universalFrame R (ι → R) ι) = ⇑twist ∘ ⇑e₁ := by
    funext z
    induction z using TensorProduct.inductionOn with
    | tmul p f =>
      ext i τ
      simp [e₁, e₂, twist, smul_eq_mul, mul_comm]
    | add x y hx hy =>
      ext i τ
      have hx' := congrFun (congrFun hx i) τ
      have hy' := congrFun (congrFun hy i) τ
      simp only [Function.comp_apply, map_add, Pi.add_apply, twist, Equiv.coe_fn_mk] at hx' hy' ⊢
      exact congrArg₂ (· + ·) hx' hy'
  have hbij : Function.Bijective (⇑e₂ ∘ ⇑(universalFrame R (ι → R) ι)) :=
    hcomp ▸ twist.bijective.comp e₁.bijective
  exact (Function.Bijective.of_comp_iff' e₂.bijective _).mp hbij

/-- The universal frame of the split algebra `ι → R` as an isomorphism of
`FrameAlgebra R (ι → R) ι`-algebras. -/
noncomputable def universalFrameEquivPi :
    FrameAlgebra R (ι → R) ι ⊗[R] (ι → R) ≃ₐ[FrameAlgebra R (ι → R) ι]
      (ι → FrameAlgebra R (ι → R) ι) :=
  AlgEquiv.ofBijective (universalFrame R (ι → R) ι) (bijective_universalFrame_pi R ι)

variable {R ι}

/-- `TauCeti.Algebra.FrameAlgebra.universalFrameEquivPi` has underlying map `universalFrame`. -/
@[simp]
theorem coe_universalFrameEquivPi :
    ⇑(universalFrameEquivPi R ι) = universalFrame R (ι → R) ι :=
  (rfl)

/-- `TauCeti.Algebra.FrameAlgebra.universalFrameEquivPi` sends `p ⊗ f` at `i` to
`p * slotAlgHom R (ι → R) i f`. -/
theorem universalFrameEquivPi_tmul (p : FrameAlgebra R (ι → R) ι) (f : ι → R) (i : ι) :
    universalFrameEquivPi R ι (p ⊗ₜ f) i = p * slotAlgHom R (ι → R) i f :=
  (rfl)

/-- **The universal frame of a locally split algebra is bijective.** If `S` becomes isomorphic to
`ι → T` after a faithfully flat extension `R → T`, then `universalFrame R S ι` is bijective. -/
theorem bijective_universalFrame_of_algEquiv_pi (T : Type*) [CommRing T] [Algebra R T]
    [Module.FaithfullyFlat R T] (e : T ⊗[R] S ≃ₐ[T] (ι → T)) :
    Function.Bijective (universalFrame R S ι) :=
  (bijective_universalFrame_baseChange_iff T).mp
    ((bijective_universalFrame_congr_iff e).mp (bijective_universalFrame_pi T ι))

/-- **The universal frame of a locally split algebra as an isomorphism.** If
`T ⊗[R] S ≃ₐ[T] (ι → T)` for a faithfully flat `R`-algebra `T`, then `FrameAlgebra R S ι ⊗[R] S`
is isomorphic to `ι → FrameAlgebra R S ι` over `FrameAlgebra R S ι`. -/
noncomputable def universalFrameEquivOfAlgEquivPi (T : Type*) [CommRing T] [Algebra R T]
    [Module.FaithfullyFlat R T] (e : T ⊗[R] S ≃ₐ[T] (ι → T)) :
    FrameAlgebra R S ι ⊗[R] S ≃ₐ[FrameAlgebra R S ι] (ι → FrameAlgebra R S ι) :=
  AlgEquiv.ofBijective (universalFrame R S ι) (bijective_universalFrame_of_algEquiv_pi T e)

/-- `TauCeti.Algebra.FrameAlgebra.universalFrameEquivOfAlgEquivPi` has underlying map
`universalFrame`. -/
@[simp]
theorem coe_universalFrameEquivOfAlgEquivPi (T : Type*) [CommRing T] [Algebra R T]
    [Module.FaithfullyFlat R T] (e : T ⊗[R] S ≃ₐ[T] (ι → T)) :
    ⇑(universalFrameEquivOfAlgEquivPi T e) = universalFrame R S ι :=
  (rfl)

/-- `TauCeti.Algebra.FrameAlgebra.universalFrameEquivOfAlgEquivPi` sends `p ⊗ s` at `i` to
`p * slotAlgHom R S i s`. -/
theorem universalFrameEquivOfAlgEquivPi_tmul (T : Type*) [CommRing T] [Algebra R T]
    [Module.FaithfullyFlat R T] (e : T ⊗[R] S ≃ₐ[T] (ι → T))
    (p : FrameAlgebra R S ι) (s : S) (i : ι) :
    universalFrameEquivOfAlgEquivPi T e (p ⊗ₜ s) i = p * slotAlgHom R S i s :=
  (rfl)

end UniversalFrame

end TauCeti.Algebra.FrameAlgebra
