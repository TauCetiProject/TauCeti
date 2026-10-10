/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.IsTensorProduct.Pushout

import Mathlib.RingTheory.Finiteness.Projective
import TauCeti.RingTheory.Extension.Presentation.Basic

/-!
# Weil restriction along a finite projective algebra

Let `A` be a commutative ring, `B` an `A`-algebra that is finitely generated and projective as an
`A`-module, so that `Spec B → Spec A` is finite locally free, and `C` a `B`-algebra of finite
presentation. The Weil restriction of `C` along `B` is the functor on `A`-algebras sending `T` to
the set `C →ₐ[B] B ⊗[A] T` of `B`-algebra homomorphisms; geometrically, it sends `Spec T` to the
set of `Spec B`-morphisms `Spec (B ⊗[A] T) → Spec C`. This file constructs an `A`-algebra of finite
presentation representing this functor, together with its universal point, and shows that its
formation commutes with an arbitrary base change `A → A'`.

## Main definitions

* `TauCeti.Algebra.WeilRestriction A B C`: an `A`-algebra representing `T ↦ (C →ₐ[B] B ⊗[A] T)`.
* `TauCeti.Algebra.WeilRestriction.universalPoint A B C`: the universal point
  `C →ₐ[B] B ⊗[A] WeilRestriction A B C`.
* `TauCeti.Algebra.WeilRestriction.homEquiv A B C T`: the bijection
  `(WeilRestriction A B C →ₐ[A] T) ≃ (C →ₐ[B] B ⊗[A] T)`, given by composing the universal point
  with `B ⊗[A] -`.
* `TauCeti.Algebra.WeilRestriction.baseChangeAlgEquiv A B C A' B' C'`: for `B' = B ⊗[A] A'` and
  `C' = C ⊗[B] B'` (expressed through `Algebra.IsPushout`), the `A'`-algebra isomorphism
  `A' ⊗[A] WeilRestriction A B C ≃ₐ[A'] WeilRestriction A' B' C'`.
* `TauCeti.Algebra.WeilRestriction.tensorHomEquiv A B D T`: for a finitely presented `A`-algebra
  `D`, the Weil restriction of `B ⊗[A] D` represents `T ↦ (D →ₐ[A] T ⊗[A] B)`, the functor of
  morphisms from `Spec B` to `Spec D` over `Spec A`.

## Main results

* `TauCeti.Algebra.WeilRestriction.homEquiv_comp`: `homEquiv` is natural in the `A`-algebra `T`.
* `TauCeti.Algebra.WeilRestriction.hom_ext`: homomorphisms out of the Weil restriction are
  determined by their effect on the universal point.
* `TauCeti.Algebra.WeilRestriction.instFinitePresentation`: the Weil restriction is of finite
  presentation over `A`.
* `TauCeti.Algebra.WeilRestriction.homEquiv_comp_baseChangeAlgEquiv`: `baseChangeAlgEquiv` is
  compatible with the universal properties: for `g : WeilRestriction A' B' C' →ₐ[A'] T`, the point
  of `C` classified by `g ∘ baseChangeAlgEquiv` restricted to `WeilRestriction A B C` is the
  restriction to `C` of the point of `C'` classified by `g`.
* `TauCeti.Algebra.WeilRestriction.tensorHomEquiv_comp`: `tensorHomEquiv` is natural in `T`.

## References

* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, §7.6.
* [The Stacks Project, Section 05Y8](https://stacks.math.columbia.edu/tag/05Y8) (restriction of
  scalars), and [Lemma 05YC](https://stacks.math.columbia.edu/tag/05YC) (base change).
-/

public noncomputable section

open Algebra TensorProduct MvPolynomial

namespace TauCeti.Algebra

namespace WeilRestriction

section Coordinates

-- A finite family `b` of generators of the `A`-module `B` with coordinate functionals `φ`, in the
-- sense that `x = ∑ j, φ j x • b j` for every `x : B`. It exists when `B` is finite projective.
private structure Coords (A B : Type*) [CommSemiring A] [AddCommMonoid B] [Module A B] where
  n : ℕ
  b : Fin n → B
  φ : Fin n → Module.Dual A B
  sum_smul (x : B) : ∑ j, φ j x • b j = x

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]

private theorem nonempty_coords [Module.Finite A B] [Module.Projective A B] :
    Nonempty (Coords A B) := by
  obtain ⟨n, p, s, -, -, hs⟩ := Module.Finite.exists_comp_eq_id_of_projective A B
  refine ⟨⟨n, fun j ↦ p (Pi.single j 1), fun j ↦ LinearMap.proj j ∘ₗ s, fun x ↦ ?_⟩⟩
  -- pull `p` out of the sum, which is then the expansion of `s x` in the standard basis
  simpa only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.id_apply, ← map_smul,
    ← map_sum, ← pi_eq_sum_univ'] using LinearMap.congr_fun hs x

-- The chosen coordinate system on a finite projective algebra.
private def coords [Module.Finite A B] [Module.Projective A B] : Coords A B :=
  (nonempty_coords A B).some

variable {A B} (T : Type*) [CommRing T] [Algebra A T]

-- The `j`-th coordinate `B ⊗[A] T → T`, sending `x ⊗ t` to `φ j x • t`.
private def Coords.coord (K : Coords A B) (j : Fin K.n) : B ⊗[A] T →ₗ[A] T :=
  lift (LinearMap.lsmul A T ∘ₗ K.φ j)

variable {T}

private lemma Coords.coord_tmul (K : Coords A B) (j : Fin K.n) (x : B) (t : T) :
    K.coord T j (x ⊗ₜ t) = K.φ j x • t := rfl

private lemma Coords.sum_tmul_coord (K : Coords A B) (z : B ⊗[A] T) :
    ∑ j, K.b j ⊗ₜ K.coord T j z = z := by
  induction z with
  | tmul x t => simp [coord_tmul, smul_tmul', ← sum_tmul, K.sum_smul]
  | add z w hz hw => simp [tmul_add, Finset.sum_add_distrib, hz, hw]

private lemma Coords.coord_lTensor (K : Coords A B) {T' : Type*} [CommRing T'] [Algebra A T']
    (g : T →ₐ[A] T') (j : Fin K.n) (z : B ⊗[A] T) :
    K.coord T' j (Algebra.TensorProduct.lTensor (S := B) B g z) = g (K.coord T j z) := by
  induction z <;> simp [coord_tmul, *]

end Coordinates

section Construction

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
  {ι σ : Type*} {T : Type*} [CommRing T] [Algebra A T]

-- The family `i ↦ ∑ j, b j ⊗ X (i, j)` in `B ⊗[A] A[X]`, where `A[X]` is the polynomial ring in
-- the variables `X (i, j)`. For a commutative `A`-algebra `T`, every family `ι → B ⊗[A] T` is its
-- image under `B ⊗[A] g` for some `g : A[X] →ₐ[A] T`.
private def pt (K : Coords A B) (i : ι) : B ⊗[A] MvPolynomial (ι × Fin K.n) A :=
  ∑ j, K.b j ⊗ₜ X (i, j)

-- The defining relations of the representing algebra. For `(i, k)`: the `k`-th coordinate of
-- `pt K i` is `X (i, k)`, i.e. the vector `X (i, ·)` is fixed by the idempotent
-- `Tⁿ → B ⊗[A] T → Tⁿ`, where `T` is the polynomial ring. For `(r, k)`: the `k`-th coordinate of
-- the relation `r` of `P` evaluated at `pt K` vanishes.
private def relation (P : Presentation B C ι σ) (K : Coords A B) :
    (ι × Fin K.n) ⊕ (σ × Fin K.n) → MvPolynomial (ι × Fin K.n) A
  | .inl (i, k) => X (i, k) - K.coord _ k (pt K i)
  | .inr (r, k) => K.coord _ k (aeval (pt K) (P.relation r))

-- The `A`-algebra representing `T ↦ (C →ₐ[B] B ⊗[A] T)` attached to the presentation `P` and the
-- coordinates `K`: polynomials in the coordinates of the generators of `P`, modulo `relation P K`.
private abbrev RepresentingAlgebra (P : Presentation B C ι σ) (K : Coords A B) :=
  MvPolynomial (ι × Fin K.n) A ⧸ Ideal.span (Set.range (relation P K))

-- The coordinates of a family of elements of `B ⊗[A] T`.
private def coordsOf (K : Coords A B) (z : ι → B ⊗[A] T) : ι × Fin K.n → T :=
  fun ij ↦ K.coord T ij.2 (z ij.1)

private lemma lTensor_aeval_coordsOf_pt (K : Coords A B) (z : ι → B ⊗[A] T) (i : ι) :
    Algebra.TensorProduct.lTensor (S := B) B (aeval (coordsOf K z)) (pt K i) = z i := by
  simp [pt, coordsOf, K.sum_tmul_coord]

private lemma aeval_coordsOf_relation (P : Presentation B C ι σ) (K : Coords A B)
    (h : C →ₐ[B] B ⊗[A] T) (q : (ι × Fin K.n) ⊕ (σ × Fin K.n)) :
    aeval (coordsOf K (h ∘ P.val)) (relation P K q) = 0 := by
  rcases q with ⟨i, k⟩ | ⟨r, k⟩
  · simp [relation, ← Coords.coord_lTensor, lTensor_aeval_coordsOf_pt, coordsOf]
  · rw [relation, ← Coords.coord_lTensor, comp_aeval_apply]
    simp [lTensor_aeval_coordsOf_pt, ← comp_aeval_apply]

-- The universal point of `RepresentingAlgebra P K`: it sends `P.val i` to the image of `pt K i`.
private def universalPointOfPresentation (P : Presentation B C ι σ) (K : Coords A B) :
    C →ₐ[B] B ⊗[A] RepresentingAlgebra P K :=
  P.lift
    (fun i ↦ Algebra.TensorProduct.lTensor (S := B) B (Ideal.Quotient.mkₐ A _) (pt K i)) fun r ↦ by
      -- expanded in the coordinates `K`, the `k`-th coordinate of the relation evaluated at
      -- `pt K` is `relation P K (.inr (r, k))`, which vanishes in the quotient
      rw [← comp_aeval_apply, ← K.sum_tmul_coord (Algebra.TensorProduct.lTensor _ _ _)]
      simp [Coords.coord_lTensor, ← relation.eq_2]

variable (T) in
-- The universal property of `RepresentingAlgebra P K`.
private def homEquivOfPresentation (P : Presentation B C ι σ) (K : Coords A B) :
    (RepresentingAlgebra P K →ₐ[A] T) ≃ (C →ₐ[B] B ⊗[A] T) where
  toFun g := (Algebra.TensorProduct.lTensor B g).comp (universalPointOfPresentation P K)
  invFun h := Ideal.Quotient.liftₐ _ (aeval (coordsOf K (h ∘ P.val))) fun _ ha ↦
    RingHom.mem_ker.1 (Ideal.span_le.2 (Set.range_subset_iff.2 (aeval_coordsOf_relation P K h)) ha)
  left_inv g := Ideal.Quotient.algHom_ext _ <| MvPolynomial.algHom_ext fun ⟨i, j⟩ ↦ by
    -- the relation `.inl (i, j)` identifies `X (i, j)` with the `j`-th coordinate of `pt K i`
    have hrel : Ideal.Quotient.mkₐ A (Ideal.span (Set.range (relation P K))) (X (i, j)) =
        Ideal.Quotient.mkₐ A _ (K.coord _ j (pt K i)) :=
      Ideal.Quotient.eq.2 (Ideal.subset_span ⟨.inl (i, j), rfl⟩)
    rw [Ideal.Quotient.liftₐ_comp, aeval_X, AlgHom.comp_apply, hrel, ← Coords.coord_lTensor]
    simp [coordsOf, universalPointOfPresentation, Presentation.lift_val, Coords.coord_lTensor]
  right_inv h := P.algHom_ext fun i ↦ by
    rw [AlgHom.comp_apply, universalPointOfPresentation, Presentation.lift_val,
      ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_id_comp, Ideal.Quotient.liftₐ_comp]
    exact lTensor_aeval_coordsOf_pt K _ i

end Construction

end WeilRestriction

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
  [Module.Finite A B] [Module.Projective A B] [FinitePresentation B C]

/-- The **Weil restriction** of a finitely presented `B`-algebra `C` along a finite projective
`A`-algebra `B`: an `A`-algebra representing the functor sending an `A`-algebra `T` to the set
`C →ₐ[B] B ⊗[A] T`, see `WeilRestriction.homEquiv`. -/
def WeilRestriction : Type _ :=
  WeilRestriction.RepresentingAlgebra (Presentation.ofFinitePresentation B C)
    (WeilRestriction.coords A B)
deriving CommRing, Algebra A

namespace WeilRestriction

/-- The universal point of the Weil restriction, corresponding to the identity of
`WeilRestriction A B C` under `WeilRestriction.homEquiv`: for every `A`-algebra `T`, each
`B`-algebra homomorphism `C →ₐ[B] B ⊗[A] T` is its composite with `B ⊗[A] g` for a unique
`g : WeilRestriction A B C →ₐ[A] T`. -/
def universalPoint : C →ₐ[B] B ⊗[A] WeilRestriction A B C :=
  universalPointOfPresentation (Presentation.ofFinitePresentation B C) (coords A B)

variable (T : Type*) [CommRing T] [Algebra A T]

/-- The universal property of the Weil restriction: the bijection between `A`-algebra homomorphisms
`g : WeilRestriction A B C →ₐ[A] T` and `B`-algebra homomorphisms `C →ₐ[B] B ⊗[A] T` that sends `g`
to the composite `C → B ⊗[A] WeilRestriction A B C → B ⊗[A] T` of the universal point with
`B ⊗[A] g`. It is natural in `T`, see `WeilRestriction.homEquiv_comp`. -/
def homEquiv : (WeilRestriction A B C →ₐ[A] T) ≃ (C →ₐ[B] B ⊗[A] T) :=
  homEquivOfPresentation T (Presentation.ofFinitePresentation B C) (coords A B)

variable {A B C T}

/-- `WeilRestriction.homEquiv` sends `g` to the composite of the universal point with
`B ⊗[A] g`. -/
@[simp]
theorem homEquiv_apply (g : WeilRestriction A B C →ₐ[A] T) :
    homEquiv A B C T g = (Algebra.TensorProduct.lTensor B g).comp (universalPoint A B C) := (rfl)

/-- Naturality of `WeilRestriction.homEquiv` in the `A`-algebra `T`: post-composing with
`h : T →ₐ[A] T'` corresponds to post-composing with `B ⊗[A] h`. -/
theorem homEquiv_comp {T' : Type*} [CommRing T'] [Algebra A T'] (g : WeilRestriction A B C →ₐ[A] T)
    (h : T →ₐ[A] T') : homEquiv A B C T' (h.comp g) =
      (Algebra.TensorProduct.lTensor B h).comp (homEquiv A B C T g) := by
  simp [Algebra.TensorProduct.map_id_comp, AlgHom.comp_assoc]

/-- Two `A`-algebra homomorphisms out of the Weil restriction are equal if they agree on the
universal point, that is, if they classify the same point `C →ₐ[B] B ⊗[A] T` under
`WeilRestriction.homEquiv`. See note [partially-applied ext lemmas]. -/
@[ext]
theorem hom_ext {g₁ g₂ : WeilRestriction A B C →ₐ[A] T}
    (h : (Algebra.TensorProduct.lTensor B g₁).comp (universalPoint A B C) =
      (Algebra.TensorProduct.lTensor B g₂).comp (universalPoint A B C)) : g₁ = g₂ :=
  (homEquiv A B C T).injective <| by simpa using h

/-- The Weil restriction of a finitely presented algebra along a finite projective algebra is of
finite presentation over `A`. -/
instance instFinitePresentation : FinitePresentation A (WeilRestriction A B C) :=
  FinitePresentation.quotient <| Submodule.fg_span <| Set.finite_range _

section BaseChange

variable (A B C) (A' B' C' : Type*) [CommRing A'] [CommRing B'] [CommRing C'] [Algebra A A']
  [Algebra A' B'] [Algebra A B'] [Algebra B B'] [IsScalarTower A A' B'] [IsScalarTower A B B']
  [IsPushout A B A' B'] [Algebra B' C'] [Algebra B C'] [Algebra C C'] [IsScalarTower B B' C']
  [IsScalarTower B C C'] [IsPushout B C B' C']

-- The base change of the universal point. Writing `W = WeilRestriction A B C`, this is the point of
-- the Weil restriction of `C'` along `B'` with values in `A' ⊗[A] W` that extends, along `C → C'`,
-- the point of `C` classified by `W → A' ⊗[A] W`, moved along
-- `B ⊗[A] (A' ⊗[A] W) ≃ B' ⊗[A'] (A' ⊗[A] W)`.
private def baseChangePoint : C' →ₐ[B'] B' ⊗[A'] (A' ⊗[A] WeilRestriction A B C) :=
  IsPushout.lift B' <| (IsPushout.cancelBaseChangeAlg A B A' B' _).symm.toAlgHom.comp <|
    homEquiv A B C _ Algebra.TensorProduct.includeRight

variable {A B C A' B' C'} [Algebra A' T] [IsScalarTower A A' T]

-- On `C`, composing `baseChangePoint` with `B' ⊗[A'] g` gives the point of `C` classified by the
-- restriction of `g` to `WeilRestriction A B C`, moved to `B' ⊗[A'] T` by `cancelBaseChangeAlg`.
private lemma lTensor_baseChangePoint_algebraMap (g : A' ⊗[A] WeilRestriction A B C →ₐ[A'] T)
    (c : C) : Algebra.TensorProduct.lTensor (S := B') B' g
        (baseChangePoint A B C A' B' C' (algebraMap C C' c)) =
      (IsPushout.cancelBaseChangeAlg A B A' B' T).symm
        (homEquiv A B C T ((g.restrictScalars A).comp Algebra.TensorProduct.includeRight) c) := by
  simp [baseChangePoint, ← IsPushout.cancelBaseChangeAlg_symm_lTensor,
    Algebra.TensorProduct.map_id_comp]

-- `A'`-algebra homomorphisms out of `A' ⊗[A] WeilRestriction A B C` are determined by their effect
-- on the base change of the universal point.
private lemma baseChange_hom_ext {g₁ g₂ : A' ⊗[A] WeilRestriction A B C →ₐ[A'] T}
    (h : (Algebra.TensorProduct.lTensor B' g₁).comp (baseChangePoint A B C A' B' C') =
      (Algebra.TensorProduct.lTensor B' g₂).comp (baseChangePoint A B C A' B' C')) : g₁ = g₂ := by
  -- `ext` applies `Algebra.TensorProduct.ext_ring` and `hom_ext`, reducing to the elements of `C`
  ext c
  simpa [lTensor_baseChangePoint_algebraMap] using congr($h (algebraMap C C' c))

variable (A B C) in
-- The `A'`-algebra homomorphism `A' ⊗[A] WeilRestriction A B C → T` classifying a `T`-point `h` of
-- the Weil restriction of `C'` along `B'` with respect to the base change of the universal point:
-- restrict `h` to `C`, transport it along `B' ⊗[A'] T ≃ B ⊗[A] T`, classify the result by
-- `homEquiv`, and extend scalars from `A` to `A'`.
private def baseChangeLift (h : C' →ₐ[B'] B' ⊗[A'] T) :
    A' ⊗[A] WeilRestriction A B C →ₐ[A'] T :=
  Algebra.TensorProduct.liftEquivRight A A' _ T <| (homEquiv A B C T).symm <|
    (IsPushout.cancelBaseChangeAlg A B A' B' T).toAlgHom.comp <|
      (h.restrictScalars B).comp (IsScalarTower.toAlgHom B C C')

private lemma lTensor_baseChangeLift_comp_baseChangePoint (h : C' →ₐ[B'] B' ⊗[A'] T) :
    (Algebra.TensorProduct.lTensor B' (baseChangeLift A B C h)).comp
      (baseChangePoint A B C A' B' C') = h := by
  refine IsPushout.algHom_ext' (R := B) (S := C) <| AlgHom.ext fun c ↦ ?_
  simp [lTensor_baseChangePoint_algebraMap, baseChangeLift]

variable (A B C A' B' C')

/-- **The Weil restriction commutes with base change.** If `B' = B ⊗[A] A'` and
`C' = C ⊗[B] B'`, as expressed by `Algebra.IsPushout A B A' B'` and `Algebra.IsPushout B C B' C'`,
this is an isomorphism of `A'`-algebras from `A' ⊗[A] WeilRestriction A B C` to the Weil
restriction of `C'` along `B'`. It is compatible with the universal properties, see
`WeilRestriction.homEquiv_comp_baseChangeAlgEquiv`. The finiteness hypotheses on `B'` and
`C'` follow from the pushouts, and are filled in by default with `Module.Finite.of_isPushout`,
`Module.Projective.of_isPushout` and `Algebra.FinitePresentation.of_isPushout`. -/
def baseChangeAlgEquiv (hfin : Module.Finite A' B' := .of_isPushout A B A' B')
    (hproj : Module.Projective A' B' := .of_isPushout A B A' B')
    (hfp : FinitePresentation B' C' := .of_isPushout B C B' C') :
    A' ⊗[A] WeilRestriction A B C ≃ₐ[A'] WeilRestriction A' B' C' :=
  -- `baseChangeLift` takes a target `T` with `[Algebra A T] [IsScalarTower A A' T]`: make the Weil
  -- restriction of `C'` along `B'` an `A`-algebra through `A → A'`
  let _ : Algebra A (WeilRestriction A' B' C') := Algebra.compHom _ (algebraMap A A')
  have _ : IsScalarTower A A' (WeilRestriction A' B' C') := .of_algebraMap_eq' rfl
  AlgEquiv.ofAlgHom (baseChangeLift A B C (universalPoint A' B' C'))
    ((homEquiv A' B' C' _).symm (baseChangePoint A B C A' B' C'))
    -- the composite on `WeilRestriction A' B' C'` fixes the universal point
    (hom_ext <| by
      simp [Algebra.TensorProduct.map_id_comp, AlgHom.comp_assoc, ← homEquiv_apply,
        lTensor_baseChangeLift_comp_baseChangePoint])
    -- the composite on `A' ⊗[A] WeilRestriction A B C` fixes `baseChangePoint`
    (baseChange_hom_ext (B' := B') (C' := C') <| by
      simp [Algebra.TensorProduct.map_id_comp, AlgHom.comp_assoc, ← homEquiv_apply,
        lTensor_baseChangeLift_comp_baseChangePoint])

variable {A B C A' B' C'} {hfin : Module.Finite A' B'} {hproj : Module.Projective A' B'}
  {hfp : FinitePresentation B' C'}

-- `baseChangeAlgEquiv` carries `baseChangePoint`, the base change of the universal point, to the
-- universal point of `WeilRestriction A' B' C'`.
private lemma lTensor_baseChangeAlgEquiv_comp_baseChangePoint :
    (Algebra.TensorProduct.lTensor B' (baseChangeAlgEquiv A B C A' B' C').toAlgHom).comp
      (baseChangePoint A B C A' B' C') = universalPoint A' B' C' := by
  simp [baseChangeAlgEquiv, AlgEquiv.toAlgHom_ofAlgHom, lTensor_baseChangeLift_comp_baseChangePoint]

/-- Compatibility of `WeilRestriction.baseChangeAlgEquiv` with the universal properties.
For `g : WeilRestriction A' B' C' →ₐ[A'] T`, let `g₀ : WeilRestriction A B C →ₐ[A] T` be the
composite of `Algebra.TensorProduct.includeRight`, `baseChangeAlgEquiv` and `g`. Then the point
`homEquiv A B C T g₀ : C →ₐ[B] B ⊗[A] T` is the composite of `algebraMap C C'`, the point
`homEquiv A' B' C' T g : C' →ₐ[B'] B' ⊗[A'] T` and the isomorphism
`Algebra.IsPushout.cancelBaseChangeAlg A B A' B' T : B' ⊗[A'] T ≃ₐ[B] B ⊗[A] T`. Here `T` is an
`A'`-algebra with a compatible `A`-algebra structure. -/
theorem homEquiv_comp_baseChangeAlgEquiv (g : WeilRestriction A' B' C' →ₐ[A'] T) :
    homEquiv A B C T (((g.comp (baseChangeAlgEquiv A B C A' B' C').toAlgHom).restrictScalars A).comp
        Algebra.TensorProduct.includeRight) =
      (IsPushout.cancelBaseChangeAlg A B A' B' T).toAlgHom.comp
        (((homEquiv A' B' C' T g).restrictScalars B).comp (IsScalarTower.toAlgHom B C C')) := by
  ext c
  refine (IsPushout.cancelBaseChangeAlg A B A' B' T).symm_apply_eq.1 ?_
  -- the universal point of `C'` is the image of `baseChangePoint` under `baseChangeAlgEquiv`
  rw [← lTensor_baseChangePoint_algebraMap (C' := C'), homEquiv_apply,
    ← lTensor_baseChangeAlgEquiv_comp_baseChangePoint (A := A) (B := B) (C := C)]
  simp [Algebra.TensorProduct.map_id_comp]

end BaseChange

section TensorHom

variable (A B D : Type*) [CommRing A] [CommRing B] [CommRing D] [Algebra A B] [Algebra A D]
  [Module.Finite A B] [Module.Projective A B] [FinitePresentation A D]
  (T : Type*) [CommRing T] [Algebra A T]

/-- The Weil restriction along `B` of the scalar extension `B ⊗[A] D` represents the functor
sending an `A`-algebra `T` to the set `D →ₐ[A] T ⊗[A] B`. Geometrically, `Spec` of it is the
scheme of morphisms from `Spec B` to `Spec D` over `Spec A`: its `T`-points are the morphisms
`Spec (T ⊗[A] B) → Spec D` over `Spec A`. It is natural in `T`, see
`WeilRestriction.tensorHomEquiv_comp`. -/
def tensorHomEquiv : (WeilRestriction A B (B ⊗[A] D) →ₐ[A] T) ≃ (D →ₐ[A] T ⊗[A] B) :=
  (homEquiv A B (B ⊗[A] D) T).trans <| (AlgHom.liftEquiv A B D (B ⊗[A] T)).symm.trans <|
    AlgEquiv.arrowCongr AlgEquiv.refl (Algebra.TensorProduct.comm A B T)

variable {A B D T}

/-- `WeilRestriction.tensorHomEquiv` sends `g` to the point `D → T ⊗[A] B` obtained by evaluating
the point `homEquiv A B (B ⊗[A] D) T g` of `B ⊗[A] D` on `1 ⊗ d`. -/
theorem tensorHomEquiv_apply (g : WeilRestriction A B (B ⊗[A] D) →ₐ[A] T) (d : D) :
    tensorHomEquiv A B D T g d =
      Algebra.TensorProduct.comm A B T (homEquiv A B (B ⊗[A] D) T g (1 ⊗ₜ d)) := (rfl)

/-- Naturality of `WeilRestriction.tensorHomEquiv` in the `A`-algebra `T`: post-composing with
`k : T →ₐ[A] T'` corresponds to post-composing with `k ⊗ B`. -/
theorem tensorHomEquiv_comp {T' : Type*} [CommRing T'] [Algebra A T']
    (g : WeilRestriction A B (B ⊗[A] D) →ₐ[A] T) (k : T →ₐ[A] T') :
    tensorHomEquiv A B D T' (k.comp g) =
      (Algebra.TensorProduct.map k (AlgHom.id A B)).comp (tensorHomEquiv A B D T g) := by
  ext d
  rw [tensorHomEquiv_apply, homEquiv_comp, AlgHom.comp_apply, AlgHom.comp_apply,
    tensorHomEquiv_apply]
  induction homEquiv A B (B ⊗[A] D) T g (1 ⊗ₜ d) using TensorProduct.inductionOn with
  | tmul b t => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end TensorHom

end WeilRestriction

end TauCeti.Algebra
