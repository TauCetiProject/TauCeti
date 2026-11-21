/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Lift
public import TauCeti.Algebra.MonoidAlgebra.Basic
public import TauCeti.RingTheory.DeltaRing.Basic

/-!
# The `δ`-structure on a monoid algebra

Let `A` be a `δ`-ring and `M` a commutative monoid. The monoid algebra `A[M]` carries a
`δ`-structure with `δ (single m a) = single (m ^ p) (δ a)`; equivalently, the coefficient
inclusion `A → A[M]` is a `δ`-map and `δ (of m) = 0` for every `m ∈ M`. Its Frobenius sends
`∑ aₘ m` to `∑ φ(aₘ) m ^ p`, so on the monoid it is the `p`-th power map. For `A = ℤ_(p)` this is
the `δ`-structure on `ℤ_(p)[M]` underlying the rank-one `δ_log`-ring `(ℤ_(p)[M], M)` of
logarithmic prismatic cohomology.

The formula `δ (single m a) = single (m ^ p) (δ a)` determines the `δ`-structure, because
`δ (x + y) - δ x - δ y` is a universal polynomial in `x` and `y`; no hypothesis on `A` is needed
for this uniqueness (`TauCeti.DeltaRing.eq_of_forall_delta_single`). The map
`x ↦ ∑ φ(aₘ) m ^ p` is a Frobenius lift for every `δ`-ring `A`
(`TauCeti.DeltaRing.isFrobeniusLift_monoidAlgebra`), and when `p` is a nonzerodivisor on `A` it is
the Frobenius of a `δ`-structure on `A[M]` (`TauCeti.DeltaRing.monoidAlgebra`), constructed through
`TauCeti.DeltaRing.ofFrobeniusLift`.

Most results are stated for an arbitrary `δ`-structure on `A[M]` satisfying the monomial formula,
so they apply to any construction of it.

## Main definitions

* `TauCeti.DeltaRing.monoidAlgebra`: the `δ`-structure on `A[M]` for a `δ`-ring `A` on which `p`
  is a nonzerodivisor.
* `TauCeti.DeltaRing.monoidAlgebraLiftEquiv`: the universal property; `δ`-maps `A[M] → B`
  correspond to pairs of a `δ`-map `A → B` and a monoid map `g : M →* B` with `δ ∘ g = 0`.

## Main results

* `TauCeti.DeltaRing.isFrobeniusLift_monoidAlgebra`: `∑ aₘ m ↦ ∑ φ(aₘ) m ^ p` lifts Frobenius.
* `TauCeti.DeltaRing.ext_monoidAlgebra`: `δ`-structures on `A[M]` agreeing on monomials agree;
  in particular the monomial formula determines the `δ`-structure
  (`TauCeti.DeltaRing.eq_of_forall_delta_single`).
* `TauCeti.DeltaRing.forall_delta_single_iff`: the monomial formula holds exactly when
  `A → A[M]` is a `δ`-map and `δ` kills `M`.
* `TauCeti.DeltaRing.frobenius_monoidAlgebra`: the Frobenius of `A[M]`.
* `TauCeti.DeltaRing.isDeltaMap_liftNCRingHom`, `TauCeti.DeltaRing.isDeltaMap_mapRingHom` and
  `TauCeti.DeltaRing.isDeltaMap_mapDomainRingHom`: the induced ring maps are `δ`-maps.

## References

* B. Bhatt and P. Scholze, *Prisms and prismatic cohomology*, Ann. of Math. 196 (2022), §2.1.
* T. Koshikawa, *Logarithmic prismatic cohomology I*, §2 (the monoid-algebra `δ_log`-rings).
-/

public section

open MonoidAlgebra

namespace TauCeti

namespace DeltaRing

variable {p : ℕ} {A M : Type*} [CommRing A] [CommMonoid M]

section FrobeniusLift

variable [Fact p.Prime] [DeltaRing p A]

variable (p A M) in
/-- For every `δ`-ring `A`, the ring endomorphism of `A[M]` sending `∑ aₘ m` to
`∑ φ(aₘ) m ^ p` lifts Frobenius modulo `p`. -/
theorem isFrobeniusLift_monoidAlgebra :
    IsFrobeniusLift p
      ((mapDomainRingHom A (powMonoidHom p : M →* M)).comp (mapRingHom M (frobenius p A))) := by
  refine ⟨fun x => ?_⟩
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp [zero_pow (Fact.out : p.Prime).ne_zero]
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b + addCorrection p x y, ?_⟩
    rw [map_add]
    linear_combination ha + hb - natCast_mul_addCorrection (p := p) x y
  | single m a =>
    refine ⟨single (m ^ p) (delta p a), ?_⟩
    simp [frobenius_apply, natCast_def, single_mul_single, mapDomain_add]

end FrobeniusLift

section Characterization

/-- Two `δ`-structures on a monoid algebra that agree on the monomials `single m a` agree. -/
theorem ext_monoidAlgebra {δ₁ δ₂ : DeltaRing p A[M]}
    (h : ∀ m a, δ₁.delta (single m a) = δ₂.delta (single m a)) : δ₁ = δ₂ := by
  refine DeltaRing.ext (funext fun x => ?_)
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [@delta_zero p _ _ δ₁, @delta_zero p _ _ δ₂]
  | add x y hx hy => rw [@delta_add p _ _ δ₁, @delta_add p _ _ δ₂, hx, hy]
  | single m a => exact h m a

/-- A ring homomorphism out of a monoid algebra is a `δ`-map as soon as it commutes with `δ` on
the monomials `single m a`. -/
theorem isDeltaMap_iff_forall_single [DeltaRing p A[M]] {B : Type*} [CommRing B] [DeltaRing p B]
    (f : A[M] →+* B) :
    IsDeltaMap p f ↔ ∀ m a, f (delta p (single m a)) = delta p (f (single m a)) := by
  refine ⟨fun hf m a => hf.map_delta _, fun h => ⟨fun x => ?_⟩⟩
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [delta_add, hx, hy]
  | single m a => exact h m a

variable [DeltaRing p A] [DeltaRing p A[M]]

/-- A `δ`-structure on `A[M]` satisfies `δ (single m a) = single (m ^ p) (δ a)` exactly when the
coefficient inclusion `A → A[M]` is a `δ`-map and `δ` vanishes on the monoid `M`. -/
theorem forall_delta_single_iff :
    (∀ (m : M) (a : A), delta p (single m a) = single (m ^ p) (delta p a)) ↔
      IsDeltaMap p (singleOneRingHom : A →+* A[M]) ∧ ∀ m, delta p (of A M m) = 0 := by
  refine ⟨fun h => ⟨⟨fun a => ?_⟩, fun m => ?_⟩, fun ⟨hC, hM⟩ m a => ?_⟩
  · simp [h]
  · simp [h]
  · have hs : single m a = singleOneRingHom a * of A M m := by simp [single_mul_single]
    rw [hs, delta_mul, hM, ← hC.map_delta]
    simp [single_mul_single]

variable (hδ : ∀ (m : M) (a : A), delta p (single m a) = single (m ^ p) (delta p a))
include hδ

/-- The coefficient inclusion `A → A[M]` is a `δ`-map. -/
theorem isDeltaMap_singleOneRingHom : IsDeltaMap p (singleOneRingHom : A →+* A[M]) :=
  ((forall_delta_single_iff).mp hδ).1

/-- `δ` vanishes on the image of the monoid. -/
theorem delta_monoidAlgebra_of (m : M) : delta p (of A M m) = 0 :=
  ((forall_delta_single_iff).mp hδ).2 m

variable [Fact p.Prime]

/-- The Frobenius of `A[M]` on monomials: `φ (single m a) = single (m ^ p) (φ a)`. -/
theorem frobenius_monoidAlgebra_single (m : M) (a : A) :
    frobenius p A[M] (single m a) = single (m ^ p) (frobenius p A a) := by
  simp [frobenius_apply, hδ, natCast_def, single_mul_single, single_add]

/-- The Frobenius of `A[M]` is the `p`-th power map on the monoid: `φ (of m) = of (m ^ p)`. -/
theorem frobenius_monoidAlgebra_of (m : M) : frobenius p A[M] (of A M m) = of A M (m ^ p) := by
  simp [frobenius_monoidAlgebra_single hδ]

/-- The Frobenius of `A[M]` sends `∑ aₘ m` to `∑ φ(aₘ) m ^ p`. -/
theorem frobenius_monoidAlgebra :
    frobenius p A[M] =
      (mapDomainRingHom A (powMonoidHom p : M →* M)).comp (mapRingHom M (frobenius p A)) :=
  ringHom_ext (fun a => by simp [frobenius_monoidAlgebra_single hδ])
    fun m => by simp [frobenius_monoidAlgebra_single hδ]

end Characterization

/-- If `δ`-structures on `A[M]` satisfy `δ (single m a) = single (m ^ p) (δ a)`, then they are
equal. No hypothesis on `A` is needed. -/
theorem eq_of_forall_delta_single [DeltaRing p A] {δ₁ δ₂ : DeltaRing p A[M]}
    (h₁ : ∀ (m : M) (a : A), δ₁.delta (single m a) = single (m ^ p) (delta p a))
    (h₂ : ∀ (m : M) (a : A), δ₂.delta (single m a) = single (m ^ p) (delta p a)) : δ₁ = δ₂ :=
  ext_monoidAlgebra fun m a => (h₁ m a).trans (h₂ m a).symm

section UniversalProperty

variable {B : Type*} [CommRing B] [DeltaRing p A] [DeltaRing p A[M]] [DeltaRing p B]
  (hδ : ∀ (m : M) (a : A), delta p (single m a) = single (m ^ p) (delta p a))
include hδ

/-- The ring map `A[M] → B` induced by a `δ`-map `f : A → B` and a monoid map `g : M →* B` with
`δ (g m) = 0` for all `m` is a `δ`-map. -/
theorem isDeltaMap_liftNCRingHom {f : A →+* B} (hf : IsDeltaMap p f) {g : M →* B}
    (hg : ∀ m, delta p (g m) = 0) :
    IsDeltaMap p (liftNCRingHom f g fun _ _ => .all _ _) := by
  refine (isDeltaMap_iff_forall_single _).mpr fun m a => ?_
  rw [hδ, liftNCRingHom_single, liftNCRingHom_single, delta_mul, hg, hf.map_delta, map_pow]
  ring

/-- A `δ`-map out of `A[M]` sends every element of the monoid to an element with `δ = 0`. -/
theorem IsDeltaMap.delta_apply_monoidAlgebra_of {F : A[M] →+* B} (hF : IsDeltaMap p F) (m : M) :
    delta p (F (of A M m)) = 0 := by
  rw [← hF.map_delta, delta_monoidAlgebra_of hδ, map_zero]

variable (p A M B) in
/-- The universal property of the `δ`-ring `A[M]`: `δ`-maps `A[M] → B` correspond to pairs of a
`δ`-map `A → B` and a monoid map `M →* B` landing in the elements with `δ = 0`. -/
noncomputable def monoidAlgebraLiftEquiv :
    {F : A[M] →+* B // IsDeltaMap p F} ≃
      {f : A →+* B // IsDeltaMap p f} × {g : M →* B // ∀ m, delta p (g m) = 0} where
  toFun F := (⟨F.val.comp singleOneRingHom, F.property.comp (isDeltaMap_singleOneRingHom hδ)⟩,
    ⟨(F.val : A[M] →* B).comp (of A M), F.property.delta_apply_monoidAlgebra_of hδ⟩)
  invFun fg := ⟨liftNCRingHom fg.1.val fg.2.val fun _ _ => .all _ _,
    isDeltaMap_liftNCRingHom hδ fg.1.property fg.2.property⟩
  left_inv F := Subtype.ext <| ringHom_ext (fun a => by simp [← one_def])
    fun m => by simp [← one_def]
  right_inv fg := by ext <;> simp

/-- The `δ`-map `A → B` attached to a `δ`-map `F : A[M] → B` is its restriction to the
coefficients. -/
@[simp]
theorem coe_monoidAlgebraLiftEquiv_apply_fst (F : {F : A[M] →+* B // IsDeltaMap p F}) :
    ((monoidAlgebraLiftEquiv p A M B hδ F).1 : A →+* B) = F.val.comp singleOneRingHom :=
  (rfl)

/-- The monoid map `M →* B` attached to a `δ`-map `F : A[M] → B` is its restriction to the
monoid. -/
@[simp]
theorem coe_monoidAlgebraLiftEquiv_apply_snd (F : {F : A[M] →+* B // IsDeltaMap p F}) :
    ((monoidAlgebraLiftEquiv p A M B hδ F).2 : M →* B) = (F.val : A[M] →* B).comp (of A M) :=
  (rfl)

/-- The `δ`-map attached to a pair `(f, g)` is `liftNCRingHom f g`. -/
@[simp]
theorem coe_monoidAlgebraLiftEquiv_symm_apply
    (fg : {f : A →+* B // IsDeltaMap p f} × {g : M →* B // ∀ m, delta p (g m) = 0}) :
    ((monoidAlgebraLiftEquiv p A M B hδ).symm fg : A[M] →+* B) =
      liftNCRingHom fg.1.val fg.2.val fun _ _ => .all _ _ :=
  (rfl)

end UniversalProperty

section Functoriality

variable {B N : Type*} [CommRing B] [CommMonoid N] [DeltaRing p A] [DeltaRing p B]

/-- A `δ`-map of coefficient rings induces a `δ`-map of monoid algebras. -/
theorem isDeltaMap_mapRingHom [DeltaRing p A[M]] [DeltaRing p B[M]]
    (hA : ∀ (m : M) (a : A), delta p (single m a) = single (m ^ p) (delta p a))
    (hB : ∀ (m : M) (b : B), delta p (single m b) = single (m ^ p) (delta p b))
    {f : A →+* B} (hf : IsDeltaMap p f) : IsDeltaMap p (mapRingHom M f) := by
  refine (isDeltaMap_iff_forall_single _).mpr fun m a => ?_
  rw [hA, mapRingHom_single, mapRingHom_single, hB, hf.map_delta]

/-- A monoid map induces a `δ`-map of monoid algebras. -/
theorem isDeltaMap_mapDomainRingHom [DeltaRing p A[M]] [DeltaRing p A[N]]
    (hM : ∀ (m : M) (a : A), delta p (single m a) = single (m ^ p) (delta p a))
    (hN : ∀ (n : N) (a : A), delta p (single n a) = single (n ^ p) (delta p a))
    (g : M →* N) : IsDeltaMap p (mapDomainRingHom A g) := by
  refine (isDeltaMap_iff_forall_single _).mpr fun m a => ?_
  simp [hM, hN]

end Functoriality

section Construction

variable [Fact p.Prime] [DeltaRing p A]

variable (M) in
/-- The `δ`-structure on the monoid algebra `A[M]` of a `δ`-ring `A` on which `p` is a
nonzerodivisor: its Frobenius sends `∑ aₘ m` to `∑ φ(aₘ) m ^ p`, and
`δ (single m a) = single (m ^ p) (δ a)` (`delta_single_monoidAlgebra`). -/
@[instance_reducible]
noncomputable def monoidAlgebra (hA : IsRegular (p : A)) : DeltaRing p A[M] :=
  ofFrobeniusLift (by simpa [natCast_def] using isRegular_single_one (M := M) hA) _
    (isFrobeniusLift_monoidAlgebra p A M)

/-- The `δ`-structure `monoidAlgebra M hA` satisfies `δ (single m a) = single (m ^ p) (δ a)`. -/
theorem delta_single_monoidAlgebra (hA : IsRegular (p : A)) (m : M) (a : A) :
    @delta p _ _ (monoidAlgebra M hA) (single m a) = single (m ^ p) (delta p a) := by
  have hreg : IsRegular (p : A[M]) := by simpa [natCast_def] using isRegular_single_one (M := M) hA
  apply hreg.left
  dsimp only
  rw [natCast_mul_delta_ofFrobeniusLift]
  simp [frobenius_apply, natCast_def, single_mul_single, mapDomain_add]

end Construction

end DeltaRing

end TauCeti
