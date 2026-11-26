/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.Symbol
import TauCeti.GroupTheory.Commutator
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.UniversalCentralExtension

/-!
# The star product of commuting elementary matrices

For an associative unital ring `R`, the projection `St(R) →* E_∞(R)` from the Steinberg group onto
the stable elementary subgroup is surjective with central kernel `K₂(R)`. If `A, B ∈ E_∞(R)`
commute, the commutator `⁅a, b⁆` of lifts `a, b ∈ St(R)` maps to `⁅A, B⁆ = 1`, so it lies in
`K₂(R)`, and it does not depend on the lifts, since two lifts of the same matrix differ by a central
element. This element `A ⋆ B ∈ K₂(R)` is the **star product** of `A` and `B`.

The star product satisfies `A ⋆ A = 1` and is skew-symmetric, multiplicative in each variable as
long as each factor commutes with the other variable, invariant under simultaneous conjugation
by any element of `GL_∞(R)`, and natural in ring homomorphisms. Conjugation invariance comes from
Whitehead's lemma: on a finite stage, conjugation by an element of `GL_∞(R)` agrees with conjugation
by an elementary matrix, which lifts to `St(R)` and fixes the central commutator.

The Steinberg symbol `{u, v}` of commuting units is the star product of `diag(u, u⁻¹, 1)` and
`diag(v, 1, v⁻¹)`. The star product calculus therefore makes the Steinberg symbol bimultiplicative
for pairwise commuting units and skew-symmetric, the latter by conjugating with the permutation
matrix exchanging the last two coordinates.

## Main definitions

* `TauCeti.AlgebraicK2.starProduct`: the star product `A ⋆ B ∈ K₂(R)` of commuting elements of
  `E_∞(R)`.

## Main results

* `TauCeti.AlgebraicK2.coe_starProduct_eq_commutatorElement`: `A ⋆ B` is the commutator of any
  lifts of `A` and `B` to `St(R)`.
* `TauCeti.AlgebraicK2.starProduct_self`, `TauCeti.AlgebraicK2.starProduct_inv`: `A ⋆ A = 1` and
  `(A ⋆ B)⁻¹ = B ⋆ A`.
* `TauCeti.AlgebraicK2.starProduct_mul_left`, `TauCeti.AlgebraicK2.starProduct_mul_right`:
  `(A₁ A₂) ⋆ B = (A₁ ⋆ B)(A₂ ⋆ B)` when `A₁` and `A₂` each commute with `B`, and dually.
* `TauCeti.AlgebraicK2.starProduct_conjNormal`: `(g A g⁻¹) ⋆ (g B g⁻¹) = A ⋆ B` for every
  `g ∈ GL_∞(R)`.
* `TauCeti.AlgebraicK2.map_starProduct`: the star product is natural in ring homomorphisms.
* `TauCeti.steinbergSymbol_eq_starProduct`: `{u, v} = diag(u, u⁻¹, 1) ⋆ diag(v, 1, v⁻¹)`.
* `TauCeti.steinbergSymbol_mul_left`, `TauCeti.steinbergSymbol_mul_right`,
  `TauCeti.steinbergSymbol_inv`: the Steinberg symbol is bimultiplicative for pairwise commuting
  units, and `{u, v}⁻¹ = {v, u}`.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §8,
  the product `A ⋆ B` and Lemma 8.2.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, §5, Steinberg symbols (p. 225).
-/

public section

noncomputable section

open scoped commutatorElement

namespace TauCeti

universe u

variable {R : Type u} [Ring R]

namespace AlgebraicK2

/-! ## The star product -/

section StarProduct

/-- The commutator of two elements of `St(R)` whose images in `E_∞(R)` commute lies in `K₂(R)`. -/
private theorem commutatorElement_mem_ker {a b : SteinbergGroup R}
    (h : Commute (SteinbergGroup.toElementarySubgroup R a)
      (SteinbergGroup.toElementarySubgroup R b)) :
    ⁅a, b⁆ ∈ (SteinbergGroup.toStableGL R).ker := by
  rw [← SteinbergGroup.ker_toElementarySubgroup]
  exact (MonoidHom.commutatorElement_mem_ker_iff _).2 h

/-- The commutator of two elements of `St(R)` whose images in `E_∞(R)` commute is central. -/
private theorem commutatorElement_mem_center {a b : SteinbergGroup R}
    (h : Commute (SteinbergGroup.toElementarySubgroup R a)
      (SteinbergGroup.toElementarySubgroup R b)) :
    ⁅a, b⁆ ∈ Subgroup.center (SteinbergGroup R) :=
  SteinbergGroup.ker_toStableGL_le_center (commutatorElement_mem_ker h)

/-- A chosen lift to `St(R)` of an element of `E_∞(R)`. -/
private def lift (A : StableGeneralLinearGroup.elementarySubgroup R) : SteinbergGroup R :=
  Function.surjInv SteinbergGroup.toElementarySubgroup_surjective A

private theorem toElementarySubgroup_lift (A : StableGeneralLinearGroup.elementarySubgroup R) :
    SteinbergGroup.toElementarySubgroup R (lift A) = A :=
  Function.surjInv_eq SteinbergGroup.toElementarySubgroup_surjective A

/-- The **star product** `A ⋆ B ∈ K₂(R)` of commuting elements `A` and `B` of the stable elementary
subgroup `E_∞(R)`: the commutator of lifts of `A` and `B` to the Steinberg group `St(R)`. It does
not depend on the lifts (`TauCeti.AlgebraicK2.coe_starProduct_eq_commutatorElement`). -/
def starProduct (A B : StableGeneralLinearGroup.elementarySubgroup R) (h : Commute A B) :
    AlgebraicK2 R :=
  ⟨⁅lift A, lift B⁆, commutatorElement_mem_ker <| by
    rwa [toElementarySubgroup_lift, toElementarySubgroup_lift]⟩

variable {A B : StableGeneralLinearGroup.elementarySubgroup R}

/-- **The star product is independent of the lifts**: for any lifts `a` and `b` to `St(R)` of
commuting `A, B ∈ E_∞(R)`, the star product `A ⋆ B` is the commutator `⁅a, b⁆`. -/
theorem coe_starProduct_eq_commutatorElement (h : Commute A B) {a b : SteinbergGroup R}
    (ha : SteinbergGroup.toElementarySubgroup R a = A)
    (hb : SteinbergGroup.toElementarySubgroup R b = B) :
    (starProduct A B h : SteinbergGroup R) = ⁅a, b⁆ :=
  MonoidHom.commutatorElement_eq_of_ker_le_center
    SteinbergGroup.isCentralExtension_toElementarySubgroup.ker_le_center
    ((toElementarySubgroup_lift A).trans ha.symm) ((toElementarySubgroup_lift B).trans hb.symm)

/-- The star product of the images of `a, b ∈ St(R)` in `E_∞(R)` is the commutator `⁅a, b⁆`. -/
@[simp]
theorem coe_starProduct_toElementarySubgroup {a b : SteinbergGroup R}
    (h : Commute (SteinbergGroup.toElementarySubgroup R a)
      (SteinbergGroup.toElementarySubgroup R b)) :
    (starProduct _ _ h : SteinbergGroup R) = ⁅a, b⁆ :=
  coe_starProduct_eq_commutatorElement h rfl rfl

/-- The star product of an element of `E_∞(R)` with itself is trivial. -/
@[simp]
theorem starProduct_self (A : StableGeneralLinearGroup.elementarySubgroup R) :
    starProduct A A (Commute.refl A) = 1 := by
  obtain ⟨a, rfl⟩ := SteinbergGroup.toElementarySubgroup_surjective A
  exact Subtype.ext <| by
    rw [coe_starProduct_toElementarySubgroup, commutatorElement_self, Subgroup.coe_one]

/-- The star product with `1` on the left is trivial. -/
@[simp]
theorem starProduct_one_left (B : StableGeneralLinearGroup.elementarySubgroup R) :
    starProduct 1 B (Commute.one_left B) = 1 := by
  obtain ⟨b, rfl⟩ := SteinbergGroup.toElementarySubgroup_surjective B
  exact Subtype.ext <| by
    rw [coe_starProduct_eq_commutatorElement _ (map_one _) rfl, commutatorElement_one_left,
      Subgroup.coe_one]

/-- The star product with `1` on the right is trivial. -/
@[simp]
theorem starProduct_one_right (A : StableGeneralLinearGroup.elementarySubgroup R) :
    starProduct A 1 (Commute.one_right A) = 1 := by
  obtain ⟨a, rfl⟩ := SteinbergGroup.toElementarySubgroup_surjective A
  exact Subtype.ext <| by
    rw [coe_starProduct_eq_commutatorElement _ rfl (map_one _), commutatorElement_one_right,
      Subgroup.coe_one]

/-- **The star product is skew-symmetric**: `(A ⋆ B)⁻¹ = B ⋆ A`. -/
@[simp]
theorem starProduct_inv (h : Commute A B) : (starProduct A B h)⁻¹ = starProduct B A h.symm := by
  obtain ⟨a, rfl⟩ := SteinbergGroup.toElementarySubgroup_surjective A
  obtain ⟨b, rfl⟩ := SteinbergGroup.toElementarySubgroup_surjective B
  refine Subtype.ext ?_
  rw [Subgroup.coe_inv, coe_starProduct_toElementarySubgroup,
    coe_starProduct_toElementarySubgroup, commutatorElement_inv]

/-- **The star product is multiplicative in its first variable**: if `A₁` and `A₂` each commute
with `B`, then `(A₁ * A₂) ⋆ B = (A₁ ⋆ B) * (A₂ ⋆ B)`. The factors `A₁` and `A₂` need not commute
with each other. -/
theorem starProduct_mul_left {A₁ A₂ : StableGeneralLinearGroup.elementarySubgroup R}
    (h₁ : Commute A₁ B) (h₂ : Commute A₂ B) :
    starProduct (A₁ * A₂) B (h₁.mul_left h₂) = starProduct A₁ B h₁ * starProduct A₂ B h₂ := by
  obtain ⟨a₁, rfl⟩ := SteinbergGroup.toElementarySubgroup_surjective A₁
  obtain ⟨a₂, rfl⟩ := SteinbergGroup.toElementarySubgroup_surjective A₂
  obtain ⟨b, rfl⟩ := SteinbergGroup.toElementarySubgroup_surjective B
  refine Subtype.ext ?_
  -- `⁅a₁ a₂, b⁆ = a₁ ⁅a₂, b⁆ a₁⁻¹ ⁅a₁, b⁆`, and `⁅a₂, b⁆` is central.
  have hc := commutatorElement_mem_center h₂
  rw [Subgroup.coe_mul, coe_starProduct_eq_commutatorElement _ (map_mul _ a₁ a₂) rfl,
    coe_starProduct_toElementarySubgroup, coe_starProduct_toElementarySubgroup,
    commutatorElement_mul_left_eq_conj_mul, Subgroup.mem_center_iff.1 hc a₁, mul_inv_cancel_right,
    Subgroup.mem_center_iff.1 hc]

/-- **The star product is multiplicative in its second variable**: if `B₁` and `B₂` each commute
with `A`, then `A ⋆ (B₁ * B₂) = (A ⋆ B₁) * (A ⋆ B₂)`. The factors `B₁` and `B₂` need not commute
with each other. -/
theorem starProduct_mul_right {B₁ B₂ : StableGeneralLinearGroup.elementarySubgroup R}
    (h₁ : Commute A B₁) (h₂ : Commute A B₂) :
    starProduct A (B₁ * B₂) (h₁.mul_right h₂) = starProduct A B₁ h₁ * starProduct A B₂ h₂ := by
  rw [← inv_inv (starProduct A (B₁ * B₂) _), starProduct_inv,
    starProduct_mul_left h₁.symm h₂.symm, mul_inv, starProduct_inv, starProduct_inv]

/-- **The star product is invariant under simultaneous conjugation by `GL_∞(R)`**: for every
`g ∈ GL_∞(R)`, `(g A g⁻¹) ⋆ (g B g⁻¹) = A ⋆ B`. -/
@[simp]
theorem starProduct_conjNormal (g : StableGeneralLinearGroup R) (h : Commute A B) :
    starProduct (MulAut.conjNormal g A) (MulAut.conjNormal g B) (h.map (MulAut.conjNormal g)) =
      starProduct A B h := by
  -- On a stage containing `A` and `B`, conjugation by `g` is conjugation by some `e ∈ E_∞(R)`,
  -- which lifts to `s ∈ St(R)`; conjugating lifts of `A` and `B` by `s` gives lifts of the
  -- conjugates, and conjugation by `s` fixes the central commutator.
  obtain ⟨n, x, y, hx, hy⟩ := StableGeneralLinearGroup.exists_of₂ (A : StableGeneralLinearGroup R) B
  obtain ⟨e, he, hconj⟩ :=
    StableGeneralLinearGroup.exists_mem_elementarySubgroup_forall_mul_mul_inv_eq g n
  obtain ⟨s, hs⟩ := SteinbergGroup.toElementarySubgroup_surjective ⟨e, he⟩
  have hs' : SteinbergGroup.toStableGL R s = e := by
    rw [← SteinbergGroup.coe_toElementarySubgroup, hs]
  obtain ⟨a, rfl⟩ := SteinbergGroup.toElementarySubgroup_surjective A
  obtain ⟨b, rfl⟩ := SteinbergGroup.toElementarySubgroup_surjective B
  have hlift {c : SteinbergGroup R} {z : GL (Fin n) R}
      (hz : StableGeneralLinearGroup.of R n z = SteinbergGroup.toElementarySubgroup R c) :
      SteinbergGroup.toElementarySubgroup R (s * c * s⁻¹) =
        MulAut.conjNormal g (SteinbergGroup.toElementarySubgroup R c) := by
    refine Subtype.ext ?_
    rw [MulAut.conjNormal_apply, SteinbergGroup.coe_toElementarySubgroup, map_mul, map_mul,
      map_inv, hs', ← SteinbergGroup.coe_toElementarySubgroup, ← hz, hconj]
  have hc := commutatorElement_mem_center h
  refine Subtype.ext ?_
  rw [coe_starProduct_eq_commutatorElement _ (hlift hx) (hlift hy),
    coe_starProduct_toElementarySubgroup, ← MulAut.conj_apply, ← MulAut.conj_apply,
    ← map_commutatorElement, MulAut.conj_apply, Subgroup.mem_center_iff.1 hc s,
    mul_inv_cancel_right]

/-- **The star product is natural**: the homomorphism of `K₂` induced by a ring homomorphism `f`
sends `A ⋆ B` to `f(A) ⋆ f(B)`. -/
@[simp]
theorem map_starProduct {S : Type*} [Ring S] (f : R →+* S) (h : Commute A B) :
    map f (starProduct A B h) =
      starProduct (StableGeneralLinearGroup.elementarySubgroupMap f A)
        (StableGeneralLinearGroup.elementarySubgroupMap f B) (h.map _) := by
  obtain ⟨a, rfl⟩ := SteinbergGroup.toElementarySubgroup_surjective A
  obtain ⟨b, rfl⟩ := SteinbergGroup.toElementarySubgroup_surjective B
  refine Subtype.ext ?_
  rw [coe_map_apply, coe_starProduct_toElementarySubgroup, map_commutatorElement,
    coe_starProduct_eq_commutatorElement _ (SteinbergGroup.toElementarySubgroup_map f a)
      (SteinbergGroup.toElementarySubgroup_map f b)]

end StarProduct

end AlgebraicK2

/-! ## The Steinberg symbol as a star product -/

section SteinbergSymbol

/-- The stably elementary matrix `diag(u, u⁻¹, 1)`. -/
private def diagInvOne (u : Rˣ) : StableGeneralLinearGroup.elementarySubgroup R :=
  ⟨StableGeneralLinearGroup.of R 3 (diagGL ![u, u⁻¹, 1]),
    StableGeneralLinearGroup.of_mem_elementarySubgroup (diagGL_inv_one_mem_elementarySubgroup u)⟩

/-- The stably elementary matrix `diag(v, 1, v⁻¹)`. -/
private def diagOneInv (v : Rˣ) : StableGeneralLinearGroup.elementarySubgroup R :=
  ⟨StableGeneralLinearGroup.of R 3 (diagGL ![v, 1, v⁻¹]),
    StableGeneralLinearGroup.of_mem_elementarySubgroup (diagGL_one_inv_mem_elementarySubgroup v)⟩

/-- Diagonal matrices with entrywise commuting entries commute in `E_∞(R)`. -/
private theorem commute_of_diagGL {A B : StableGeneralLinearGroup.elementarySubgroup R}
    {s t : Fin 3 → Rˣ} (hA : (A : StableGeneralLinearGroup R) =
      StableGeneralLinearGroup.of R 3 (diagGL s))
    (hB : (B : StableGeneralLinearGroup R) = StableGeneralLinearGroup.of R 3 (diagGL t))
    (h : ∀ i, Commute (s i) (t i)) : Commute A B := by
  refine Commute.of_map (f := Subgroup.subtype _) Subtype.coe_injective ?_
  rw [Subgroup.coe_subtype, hA, hB]
  exact ((Pi.commute_iff.2 h).map diagGL).map (StableGeneralLinearGroup.of R 3)

private theorem commute_diagInvOne_diagOneInv {u v : Rˣ} (h : Commute u v) :
    Commute (diagInvOne u) (diagOneInv v) :=
  commute_of_diagGL rfl rfl fun i ↦ by fin_cases i <;> simp [h]

/-- **The Steinberg symbol is a star product**: for commuting units `u` and `v`, `{u, v}` is the
star product of `diag(u, u⁻¹, 1)` and `diag(v, 1, v⁻¹)` in `E_∞(R)`. -/
theorem steinbergSymbol_eq_starProduct {u v : Rˣ} (h : Commute u v)
    {A B : StableGeneralLinearGroup.elementarySubgroup R}
    (hA : (A : StableGeneralLinearGroup R) = StableGeneralLinearGroup.of R 3 (diagGL ![u, u⁻¹, 1]))
    (hB : (B : StableGeneralLinearGroup R) = StableGeneralLinearGroup.of R 3 (diagGL ![v, 1, v⁻¹]))
    (hAB : Commute A B) :
    steinbergSymbol u v h = AlgebraicK2.starProduct A B hAB := by
  obtain ⟨a, rfl⟩ := SteinbergGroup.toElementarySubgroup_surjective A
  obtain ⟨b, rfl⟩ := SteinbergGroup.toElementarySubgroup_surjective B
  refine Subtype.ext ?_
  rw [AlgebraicK2.coe_starProduct_toElementarySubgroup]
  exact coe_steinbergSymbol_eq_commutatorElement h
    ((SteinbergGroup.coe_toElementarySubgroup a).symm.trans hA)
    ((SteinbergGroup.coe_toElementarySubgroup b).symm.trans hB)

private theorem steinbergSymbol_eq_starProduct_diag {u v : Rˣ} (h : Commute u v) :
    steinbergSymbol u v h =
      AlgebraicK2.starProduct (diagInvOne u) (diagOneInv v) (commute_diagInvOne_diagOneInv h) :=
  steinbergSymbol_eq_starProduct h rfl rfl _

/-- **The Steinberg symbol is skew-symmetric**: for commuting units `u` and `v`,
`{u, v}⁻¹ = {v, u}`. -/
@[simp]
theorem steinbergSymbol_inv {u v : Rˣ} (h : Commute u v) :
    (steinbergSymbol u v h)⁻¹ = steinbergSymbol v u h.symm := by
  -- `{u, v}⁻¹ = diag(v, 1, v⁻¹) ⋆ diag(u, u⁻¹, 1)`, and conjugating by the permutation matrix `g`
  -- exchanging the last two coordinates turns this into `diag(v, v⁻¹, 1) ⋆ diag(u, 1, u⁻¹)`.
  let g := StableGeneralLinearGroup.of R 3 (permutationGL (Equiv.swap (1 : Fin 3) 2))
  have hswap (s : Fin 3 → Rˣ) : g * StableGeneralLinearGroup.of R 3 (diagGL s) * g⁻¹ =
      StableGeneralLinearGroup.of R 3 (diagGL ![s 0, s 2, s 1]) := by
    rw [← map_inv, ← map_mul, ← map_mul, permutationGL_mul_diagGL_mul_inv]
    congr 2
    ext i : 1
    fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
  rw [steinbergSymbol_eq_starProduct_diag, AlgebraicK2.starProduct_inv,
    ← AlgebraicK2.starProduct_conjNormal g]
  refine steinbergSymbol_eq_starProduct h.symm ?_ ?_ _ |>.symm
  · rw [MulAut.conjNormal_apply]
    exact (hswap _).trans (by simp)
  · rw [MulAut.conjNormal_apply]
    exact (hswap _).trans (by simp)

/-- **The Steinberg symbol is multiplicative in its first variable**: for pairwise commuting units
`u₁`, `u₂` and `v`, `{u₁ u₂, v} = {u₁, v} {u₂, v}`. -/
theorem steinbergSymbol_mul_left {u₁ u₂ v : Rˣ} (h₁₂ : Commute u₁ u₂) (h₁ : Commute u₁ v)
    (h₂ : Commute u₂ v) :
    steinbergSymbol (u₁ * u₂) v (h₁.mul_left h₂) =
      steinbergSymbol u₁ v h₁ * steinbergSymbol u₂ v h₂ := by
  have hmul : diagInvOne (u₁ * u₂) = diagInvOne u₁ * diagInvOne u₂ := by
    refine Subtype.ext ?_
    simp only [diagInvOne, Subgroup.coe_mul, ← map_mul]
    congr 2
    ext i : 1
    fin_cases i <;> simp [mul_inv_rev, h₁₂.inv_inv.eq]
  rw [steinbergSymbol_eq_starProduct_diag, steinbergSymbol_eq_starProduct_diag,
    steinbergSymbol_eq_starProduct_diag, ← AlgebraicK2.starProduct_mul_left]
  simp only [hmul]

/-- **The Steinberg symbol is multiplicative in its second variable**: for pairwise commuting units
`u`, `v₁` and `v₂`, `{u, v₁ v₂} = {u, v₁} {u, v₂}`. -/
theorem steinbergSymbol_mul_right {u v₁ v₂ : Rˣ} (h₁₂ : Commute v₁ v₂) (h₁ : Commute u v₁)
    (h₂ : Commute u v₂) :
    steinbergSymbol u (v₁ * v₂) (h₁.mul_right h₂) =
      steinbergSymbol u v₁ h₁ * steinbergSymbol u v₂ h₂ := by
  rw [← inv_inv (steinbergSymbol u (v₁ * v₂) _), steinbergSymbol_inv,
    steinbergSymbol_mul_left h₁₂ h₁.symm h₂.symm, mul_inv, steinbergSymbol_inv, steinbergSymbol_inv]

end SteinbergSymbol

end TauCeti
