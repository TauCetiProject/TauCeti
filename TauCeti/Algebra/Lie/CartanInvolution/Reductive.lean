/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Basic
import Mathlib.LinearAlgebra.Projection
import TauCeti.Algebra.Lie.Reductive.Basic

/-!
# Reductive Cartan involutions

A **reductive Cartan involution** of a real Lie algebra `L` is an involutive Lie algebra
automorphism `θ : L ≃ₗ⁅ℝ⁆ L` whose restriction to the derived ideal `⁅L, L⁆` is a Cartan
involution (`TauCeti.IsReductiveCartanInvolution`).

Because the derived ideal has a Cartan involution, it is finite-dimensional, Killing, and
semisimple, which forces `L` to be reductive (`LieAlgebra.HasCentralRadical ℝ L`). In finite
dimension `L = Z(L) ⊕ ⁅L, L⁆`, `θ` preserves both summands, and the `-1`-eigenspace splits as
`cartanP θ = (cartanP θ ∩ Z(L)) ⊕ (cartanP θ ∩ ⁅L, L⁆)`. Conversely, whenever `L = Z(L) ⊕ ⁅L, L⁆`,
any involutive linear automorphism of `Z(L)` and any Cartan involution of `⁅L, L⁆` assemble into
a reductive Cartan involution of `L`.

## Main definitions

* `LieEquiv.restrictDerived`, `LieEquiv.restrictCenter`: restriction of a Lie algebra equivalence
  to the derived ideal and the centre.
* `TauCeti.lieEquivOfIsComplCenterDerived`: assembly of a Lie automorphism from automorphisms of
  the centre and derived ideal when they are complementary.
* `TauCeti.IsReductiveCartanInvolution`: predicate for a reductive Cartan involution.

## Main results

* `TauCeti.IsCartanInvolution.isReductiveCartanInvolution`: every Cartan involution is a
  reductive Cartan involution.
* `TauCeti.IsReductiveCartanInvolution.hasCentralRadical` and
  `TauCeti.IsReductiveCartanInvolution.isCompl_center_derivedSeries`: a real Lie algebra admitting
  a reductive Cartan involution is reductive and splits into centre and derived ideal.
* `TauCeti.IsReductiveCartanInvolution.sup_cartanP_inf_center_derivedSeries`: the `-1`-eigenspace
  splits into its central and derived parts.
* `TauCeti.isReductiveCartanInvolution_of_isLieAbelian`: every involution of an abelian real Lie
  algebra is a reductive Cartan involution.
* `TauCeti.isReductiveCartanInvolution_lieEquivOfIsComplCenterDerived`: extension of a Cartan
  involution on `⁅L, L⁆` by an arbitrary involution of `Z(L)`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VI, §2.
-/

public section

open LieAlgebra

/-! ### Restriction of Lie equivalences to characteristic ideals -/

namespace LieEquiv

variable {R L L' L'' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L'] [LieRing L''] [LieAlgebra R L'']

/-- A Lie equivalence preserves membership in each term of the derived series. -/
@[simp]
theorem apply_mem_derivedSeries_iff (e : L ≃ₗ⁅R⁆ L') {k : ℕ} {x : L} :
    e x ∈ derivedSeries R L' k ↔ x ∈ derivedSeries R L k := by
  constructor
  · intro hx
    have h := (LieIdeal.derivedSeries_map_le (f := e.symm.toLieHom) k) (LieIdeal.mem_map hx)
    simpa using h
  · intro hx
    exact (LieIdeal.derivedSeries_map_le (f := e.toLieHom) k) (LieIdeal.mem_map hx)

/-- A Lie equivalence maps each term of the derived series onto the corresponding term of the
derived series of the codomain. -/
theorem map_derivedSeries (e : L ≃ₗ⁅R⁆ L') (k : ℕ) :
    (derivedSeries R L k).toLieSubalgebra.map e.toLieHom =
      (derivedSeries R L' k).toLieSubalgebra := by
  ext y
  rw [LieSubalgebra.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact e.apply_mem_derivedSeries_iff.mpr hx
  · intro hy
    exact ⟨e.symm y, e.symm.apply_mem_derivedSeries_iff.mpr hy, e.apply_symm_apply y⟩

/-- A Lie equivalence preserves membership in the centre. -/
theorem apply_mem_center_iff (e : L ≃ₗ⁅R⁆ L') {x : L} :
    e x ∈ center R L' ↔ x ∈ center R L := by
  simp only [LieModule.mem_maxTrivSubmodule]
  constructor
  · intro hx y
    apply e.injective
    simp only [LieEquiv.coe_toLieHom, e.map_lie, map_zero]
    exact hx (e y)
  · intro hx y'
    obtain ⟨y, rfl⟩ := e.surjective y'
    simp only [LieEquiv.coe_toLieHom]
    rw [← e.map_lie, hx y, map_zero]

/-- A Lie equivalence maps the centre onto the centre. -/
theorem map_center (e : L ≃ₗ⁅R⁆ L') :
    (center R L).toLieSubalgebra.map e.toLieHom = (center R L').toLieSubalgebra := by
  ext y
  rw [LieSubalgebra.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact e.apply_mem_center_iff.mpr hx
  · intro hy
    exact ⟨e.symm y, e.symm.apply_mem_center_iff.mpr hy, e.apply_symm_apply y⟩

/-- The restriction of a Lie algebra equivalence to the derived ideal `⁅L, L⁆`. -/
def restrictDerived (e : L ≃ₗ⁅R⁆ L') : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L' 1 :=
  e.ofSubalgebras (derivedSeries R L 1).toLieSubalgebra (derivedSeries R L' 1).toLieSubalgebra
    (e.map_derivedSeries 1)

/-- The underlying value of `restrictDerived` is `e`. -/
@[simp]
theorem coe_restrictDerived (e : L ≃ₗ⁅R⁆ L') (x : derivedSeries R L 1) :
    (e.restrictDerived x : L') = e x :=
  e.ofSubalgebras_apply (derivedSeries R L 1).toLieSubalgebra
    (derivedSeries R L' 1).toLieSubalgebra (e.map_derivedSeries 1) x

/-- The underlying value of `restrictDerived.symm` is `e.symm`. -/
@[simp]
theorem coe_restrictDerived_symm (e : L ≃ₗ⁅R⁆ L') (y : derivedSeries R L' 1) :
    (e.restrictDerived.symm y : L) = e.symm y :=
  e.ofSubalgebras_symm_apply (derivedSeries R L 1).toLieSubalgebra
    (derivedSeries R L' 1).toLieSubalgebra (e.map_derivedSeries 1) y

/-- Restricting the identity equivalence to the derived ideal gives the identity. -/
@[simp]
theorem restrictDerived_refl :
    (LieEquiv.refl : L ≃ₗ⁅R⁆ L).restrictDerived = LieEquiv.refl := by
  ext x
  simp

/-- Restricting a composite equivalence to the derived ideal is the composite of restrictions. -/
@[simp]
theorem restrictDerived_trans (e₁ : L ≃ₗ⁅R⁆ L') (e₂ : L' ≃ₗ⁅R⁆ L'') :
    (e₁.trans e₂).restrictDerived = e₁.restrictDerived.trans e₂.restrictDerived := by
  ext x
  simp

/-- Restricting the inverse equivalence to the derived ideal is the inverse of the restriction. -/
@[simp]
theorem restrictDerived_symm (e : L ≃ₗ⁅R⁆ L') :
    e.symm.restrictDerived = e.restrictDerived.symm := by
  ext x
  simp

/-- The restriction of a Lie algebra equivalence to the centre. -/
def restrictCenter (e : L ≃ₗ⁅R⁆ L') : center R L ≃ₗ⁅R⁆ center R L' :=
  e.ofSubalgebras (center R L).toLieSubalgebra (center R L').toLieSubalgebra e.map_center

/-- The underlying value of `restrictCenter` is `e`. -/
@[simp]
theorem coe_restrictCenter (e : L ≃ₗ⁅R⁆ L') (x : center R L) :
    (e.restrictCenter x : L') = e x :=
  e.ofSubalgebras_apply (center R L).toLieSubalgebra (center R L').toLieSubalgebra e.map_center x

/-- The underlying value of `restrictCenter.symm` is `e.symm`. -/
@[simp]
theorem coe_restrictCenter_symm (e : L ≃ₗ⁅R⁆ L') (y : center R L') :
    (e.restrictCenter.symm y : L) = e.symm y :=
  e.ofSubalgebras_symm_apply (center R L).toLieSubalgebra (center R L').toLieSubalgebra
    e.map_center y

/-- Restricting the identity equivalence to the centre gives the identity. -/
@[simp]
theorem restrictCenter_refl :
    (LieEquiv.refl : L ≃ₗ⁅R⁆ L).restrictCenter = LieEquiv.refl := by
  ext x
  simp

/-- Restricting a composite equivalence to the centre is the composite of restrictions. -/
@[simp]
theorem restrictCenter_trans (e₁ : L ≃ₗ⁅R⁆ L') (e₂ : L' ≃ₗ⁅R⁆ L'') :
    (e₁.trans e₂).restrictCenter = e₁.restrictCenter.trans e₂.restrictCenter := by
  ext x
  simp

/-- Restricting the inverse equivalence to the centre is the inverse of the restriction. -/
@[simp]
theorem restrictCenter_symm (e : L ≃ₗ⁅R⁆ L') :
    e.symm.restrictCenter = e.restrictCenter.symm := by
  ext x
  simp

end LieEquiv

namespace TauCeti

/-! ### Assembly on a centre/derived direct sum -/

section Assembly

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- Given a Lie algebra `L` decomposed as a direct sum of its centre and derived ideal, an
automorphism of the centre and an automorphism of the derived ideal assemble into an automorphism
of `L`. -/
noncomputable def lieEquivOfIsComplCenterDerived
    (hc : IsCompl (center R L) (derivedSeries R L 1))
    (eZ : center R L ≃ₗ[R] center R L)
    (eD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) :
    L ≃ₗ⁅R⁆ L :=
  let a := Submodule.prodEquivOfIsCompl (center R L).toSubmodule
    (derivedSeries R L 1).toSubmodule (LieSubmodule.isCompl_toSubmodule.mpr hc)
  let eLin : L ≃ₗ[R] L := (a.symm.trans (eZ.prodCongr eD.toLinearEquiv)).trans a
  { eLin with
    map_lie' := by
      intro x y
      obtain ⟨⟨z₁, d₁⟩, rfl⟩ := a.surjective x
      obtain ⟨⟨z₂, d₂⟩, rfl⟩ := a.surjective y
      have hz (z : center R L) (w : L) : ⁅(z : L), w⁆ = 0 := by
        rw [← lie_skew, (LieModule.mem_maxTrivSubmodule R L L z).mp z.property w, neg_zero]
      have hz' (z : center R L) (w : L) : ⁅w, (z : L)⁆ = 0 :=
        (LieModule.mem_maxTrivSubmodule R L L z).mp z.property w
      have ha (z : (center R L).toSubmodule) (d : (derivedSeries R L 1).toSubmodule) :
          a (z, d) = (z : L) + (d : L) := Submodule.coe_prodEquivOfIsCompl' _ _ _ _
      have he (z : center R L) (d : derivedSeries R L 1) :
          eLin ((z : L) + (d : L)) = (eZ z : L) + (eD d : L) := by
        have hzd : (z : L) + (d : L) = a (z, d) := (ha z d).symm
        rw [hzd]
        simp only [eLin, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
          LinearEquiv.prodCongr_apply, LieEquiv.coe_toLinearEquiv]
        exact ha (eZ z) (eD d)
      let d₁' : derivedSeries R L 1 := ⟨d₁.1, d₁.2⟩
      let d₂' : derivedSeries R L 1 := ⟨d₂.1, d₂.2⟩
      have hbr : ((⁅d₁', d₂'⁆ : derivedSeries R L 1) : L) = ⁅(d₁' : L), (d₂' : L)⁆ := rfl
      have hbr_eD : ((eD ⁅d₁', d₂'⁆ : derivedSeries R L 1) : L) =
          ⁅((eD d₁' : derivedSeries R L 1) : L), ((eD d₂' : derivedSeries R L 1) : L)⁆ := by
        rw [eD.map_lie]
        rfl
      have hlie_lhs : ⁅a (z₁, d₁), a (z₂, d₂)⁆ =
          ((0 : center R L) : L) + ((⁅d₁', d₂'⁆ : derivedSeries R L 1) : L) := by
        rw [ha z₁ d₁, ha z₂ d₂, add_lie, lie_add, lie_add, hz z₁, hz z₁, hz' z₂, zero_add,
          zero_add, zero_add, ZeroMemClass.coe_zero, zero_add, hbr]
      have hlie_rhs : ⁅(eZ z₁ : L) + (eD d₁' : L), (eZ z₂ : L) + (eD d₂' : L)⁆ =
          ((eD ⁅d₁', d₂'⁆ : derivedSeries R L 1) : L) := by
        rw [add_lie, lie_add, lie_add, hz (eZ z₁), hz (eZ z₁), hz' (eZ z₂), zero_add, zero_add,
          zero_add, hbr_eD]
      -- Unfold the underlying linear equivalence of the assembled map to rewrite by `he`.
      change eLin ⁅a (z₁, d₁), a (z₂, d₂)⁆ = ⁅eLin (a (z₁, d₁)), eLin (a (z₂, d₂))⁆
      rw [hlie_lhs, he 0 ⁅d₁', d₂'⁆, map_zero, ZeroMemClass.coe_zero, zero_add, ha z₁ d₁,
        ha z₂ d₂, he z₁ d₁', he z₂ d₂', hlie_rhs] }

/-- On a central element, `lieEquivOfIsComplCenterDerived` acts as `eZ`. -/
@[simp]
theorem lieEquivOfIsComplCenterDerived_apply_center
    (hc : IsCompl (center R L) (derivedSeries R L 1))
    (eZ : center R L ≃ₗ[R] center R L)
    (eD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) (z : center R L) :
    lieEquivOfIsComplCenterDerived hc eZ eD (z : L) = (eZ z : L) := by
  let a := Submodule.prodEquivOfIsCompl (center R L).toSubmodule
    (derivedSeries R L 1).toSubmodule (LieSubmodule.isCompl_toSubmodule.mpr hc)
  have hz : (z : L) = a (z, 0) := by
    rw [Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero]
  -- Evaluate the bundled equivalence on the underlying linear equivalence.
  change a ((eZ.prodCongr eD.toLinearEquiv) (a.symm (z : L))) = (eZ z : L)
  rw [hz, LinearEquiv.symm_apply_apply]
  simp [a, Submodule.coe_prodEquivOfIsCompl']

/-- On an element of the derived ideal, `lieEquivOfIsComplCenterDerived` acts as `eD`. -/
@[simp]
theorem lieEquivOfIsComplCenterDerived_apply_derivedSeries
    (hc : IsCompl (center R L) (derivedSeries R L 1))
    (eZ : center R L ≃ₗ[R] center R L)
    (eD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) (d : derivedSeries R L 1) :
    lieEquivOfIsComplCenterDerived hc eZ eD (d : L) = (eD d : L) := by
  let a := Submodule.prodEquivOfIsCompl (center R L).toSubmodule
    (derivedSeries R L 1).toSubmodule (LieSubmodule.isCompl_toSubmodule.mpr hc)
  have hd : (d : L) = a (0, d) := by
    rw [Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, zero_add]
  -- Evaluate the bundled equivalence on the underlying linear equivalence.
  change a ((eZ.prodCongr eD.toLinearEquiv) (a.symm (d : L))) = (eD d : L)
  rw [hd, LinearEquiv.symm_apply_apply]
  simp [a, Submodule.coe_prodEquivOfIsCompl']

/-- Restricting `lieEquivOfIsComplCenterDerived` to the derived ideal recovers `eD`. -/
@[simp]
theorem restrictDerived_lieEquivOfIsComplCenterDerived
    (hc : IsCompl (center R L) (derivedSeries R L 1))
    (eZ : center R L ≃ₗ[R] center R L)
    (eD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) :
    (lieEquivOfIsComplCenterDerived hc eZ eD).restrictDerived = eD := by
  ext d
  simp

/-- Restricting `lieEquivOfIsComplCenterDerived` to the centre agrees with `eZ` on underlying
elements. -/
@[simp]
theorem restrictCenter_lieEquivOfIsComplCenterDerived_apply
    (hc : IsCompl (center R L) (derivedSeries R L 1))
    (eZ : center R L ≃ₗ[R] center R L)
    (eD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) (z : center R L) :
    (lieEquivOfIsComplCenterDerived hc eZ eD).restrictCenter z = eZ z := by
  apply Subtype.ext
  simp

end Assembly

/-! ### Reductive Cartan involutions -/

section ReductiveReal

variable {L L' : Type*} [LieRing L] [LieAlgebra ℝ L] [LieRing L'] [LieAlgebra ℝ L']

/-- A **reductive Cartan involution** of a real Lie algebra `L`: an involutive automorphism whose
restriction to the derived ideal `⁅L, L⁆` is a Cartan involution. -/
def IsReductiveCartanInvolution (θ : L ≃ₗ⁅ℝ⁆ L) : Prop :=
  (∀ x, θ (θ x) = x) ∧ IsCartanInvolution θ.restrictDerived

/-- Characterization of a reductive Cartan involution. -/
theorem isReductiveCartanInvolution_iff {θ : L ≃ₗ⁅ℝ⁆ L} :
    IsReductiveCartanInvolution θ ↔ (∀ x, θ (θ x) = x) ∧ IsCartanInvolution θ.restrictDerived :=
  Iff.rfl

/-- Every Cartan involution of a real Lie algebra is a reductive Cartan involution. -/
theorem IsCartanInvolution.isReductiveCartanInvolution {θ : L ≃ₗ⁅ℝ⁆ L}
    (hθ : IsCartanInvolution θ) : IsReductiveCartanInvolution θ := by
  refine ⟨hθ.apply_apply, ?_⟩
  have hmem : ∀ x : L, x ∈ derivedSeries ℝ L 1 := fun x ↦ by
    rw [hθ.derivedSeries_one_eq_top]
    exact LieSubmodule.mem_top x
  let e : derivedSeries ℝ L 1 ≃ₗ⁅ℝ⁆ L :=
    LieEquiv.ofBijective (derivedSeries ℝ L 1).incl
      ⟨Subtype.val_injective, fun x ↦ ⟨⟨x, hmem x⟩, rfl⟩⟩
  have he (y : derivedSeries ℝ L 1) : e y = (y : L) := rfl
  have heq : ((e.symm.trans θ.restrictDerived).trans e) = θ := by
    ext x
    rw [LieEquiv.trans_apply, LieEquiv.trans_apply, he, LieEquiv.coe_restrictDerived, ← he,
      e.apply_symm_apply]
  exact (IsCartanInvolution.conj_iff e).mp (heq.symm ▸ hθ)

namespace IsReductiveCartanInvolution

variable {θ : L ≃ₗ⁅ℝ⁆ L}

/-- A reductive Cartan involution is involutive. -/
theorem involutive (hθ : IsReductiveCartanInvolution θ) : Function.Involutive θ :=
  hθ.1

/-- Applying a reductive Cartan involution twice is the identity. -/
theorem apply_apply (hθ : IsReductiveCartanInvolution θ) (x : L) : θ (θ x) = x :=
  hθ.1 x

/-- A reductive Cartan involution is its own inverse. -/
theorem symm_eq_self (hθ : IsReductiveCartanInvolution θ) : θ.symm = θ := by
  ext x
  rw [LieEquiv.symm_apply_eq, hθ.apply_apply]

/-- The restriction of a reductive Cartan involution to the derived ideal is a Cartan
involution. -/
theorem isCartanInvolution_restrictDerived (hθ : IsReductiveCartanInvolution θ) :
    IsCartanInvolution θ.restrictDerived :=
  hθ.2

/-- The derived ideal of a Lie algebra admitting a reductive Cartan involution is Killing. -/
theorem isKilling_derivedSeries (hθ : IsReductiveCartanInvolution θ) :
    IsKilling ℝ (derivedSeries ℝ L 1) :=
  hθ.2.isKilling

/-- The derived ideal of a Lie algebra admitting a reductive Cartan involution is
finite-dimensional. -/
theorem finiteDimensional_derivedSeries (hθ : IsReductiveCartanInvolution θ) :
    FiniteDimensional ℝ (derivedSeries ℝ L 1) :=
  hθ.2.finiteDimensional

/-- The derived ideal of a Lie algebra admitting a reductive Cartan involution is semisimple. -/
theorem isSemisimple_derivedSeries (hθ : IsReductiveCartanInvolution θ) :
    IsSemisimple ℝ (derivedSeries ℝ L 1) :=
  hθ.2.isSemisimple

/-- A real Lie algebra admitting a reductive Cartan involution is reductive (its radical equals
its centre). -/
theorem hasCentralRadical (hθ : IsReductiveCartanInvolution θ) : HasCentralRadical ℝ L :=
  let _ := hθ.isSemisimple_derivedSeries
  hasCentralRadical_of_hasTrivialRadical_derivedSeries ℝ L

/-- A finite-dimensional real Lie algebra admitting a reductive Cartan involution splits as the
direct sum of its centre and its derived ideal. -/
theorem isCompl_center_derivedSeries [FiniteDimensional ℝ L] (hθ : IsReductiveCartanInvolution θ) :
    IsCompl (center ℝ L) (derivedSeries ℝ L 1) :=
  let _ := hθ.isSemisimple_derivedSeries
  isCompl_center_derivedSeries_of_hasTrivialRadical_derivedSeries ℝ L

/-- The central and derived parts of `cartanP θ` are disjoint. -/
theorem disjoint_cartanP_inf_center_derivedSeries (hθ : IsReductiveCartanInvolution θ) :
    Disjoint (cartanP θ ⊓ (center ℝ L).toSubmodule)
      (cartanP θ ⊓ (derivedSeries ℝ L 1).toSubmodule) := by
  have _ := hθ.isSemisimple_derivedSeries
  have hinf : center ℝ L ⊓ derivedSeries ℝ L 1 = ⊥ := by
    simp
  have hdisj : Disjoint (center ℝ L).toSubmodule (derivedSeries ℝ L 1).toSubmodule := by
    rw [disjoint_iff, ← LieSubmodule.inf_toSubmodule, hinf, LieSubmodule.bot_toSubmodule]
  exact hdisj.mono inf_le_right inf_le_right

/-- For a reductive Cartan involution of a finite-dimensional real Lie algebra, `cartanP θ` splits
as the direct sum `(cartanP θ ∩ Z(L)) ⊕ (cartanP θ ∩ ⁅L, L⁆)`. -/
theorem sup_cartanP_inf_center_derivedSeries [FiniteDimensional ℝ L]
    (hθ : IsReductiveCartanInvolution θ) :
    (cartanP θ ⊓ (center ℝ L).toSubmodule) ⊔ (cartanP θ ⊓ (derivedSeries ℝ L 1).toSubmodule) =
      cartanP θ := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) fun x hx ↦ ?_
  have hc := LieSubmodule.isCompl_toSubmodule.mpr hθ.isCompl_center_derivedSeries
  let a := Submodule.prodEquivOfIsCompl (center ℝ L).toSubmodule
    (derivedSeries ℝ L 1).toSubmodule hc
  obtain ⟨⟨z, d⟩, hzd⟩ := a.surjective x
  have hsum : (z : L) + (d : L) = x := by
    simpa only [a, Submodule.coe_prodEquivOfIsCompl'] using hzd
  have hθz : θ (z : L) ∈ center ℝ L := θ.apply_mem_center_iff.mpr z.property
  have hθd : θ (d : L) ∈ derivedSeries ℝ L 1 := θ.apply_mem_derivedSeries_iff.mpr d.property
  have hneg : (⟨θ (z : L), hθz⟩, ⟨θ (d : L), hθd⟩) =
      ((-z : center ℝ L), (-d : derivedSeries ℝ L 1)) := by
    apply a.injective
    simp only [a, Submodule.coe_prodEquivOfIsCompl', ← map_add, hsum, mem_cartanP.mp hx,
      Submodule.coe_neg]
    rw [← hsum, neg_add]
  have hzP : (z : L) ∈ cartanP θ := by
    rw [mem_cartanP]
    exact congrArg (fun p : (center ℝ L) × derivedSeries ℝ L 1 ↦ (p.1 : L)) hneg
  have hdP : (d : L) ∈ cartanP θ := by
    rw [mem_cartanP]
    exact congrArg (fun p : (center ℝ L) × derivedSeries ℝ L 1 ↦ (p.2 : L)) hneg
  rw [← hsum]
  exact Submodule.add_mem_sup ⟨hzP, z.property⟩ ⟨hdP, d.property⟩

/-- Transporting a reductive Cartan involution along a Lie equivalence yields a reductive Cartan
involution. -/
theorem conj (hθ : IsReductiveCartanInvolution θ) (e : L ≃ₗ⁅ℝ⁆ L') :
    IsReductiveCartanInvolution ((e.symm.trans θ).trans e) := by
  refine ⟨fun x ↦ by simp [hθ.apply_apply], ?_⟩
  rw [LieEquiv.restrictDerived_trans, LieEquiv.restrictDerived_trans, LieEquiv.restrictDerived_symm]
  exact hθ.2.conj e.restrictDerived

/-- Conjugation by a Lie algebra equivalence preserves the reductive Cartan-involution property. -/
theorem conj_iff (e : L ≃ₗ⁅ℝ⁆ L') :
    IsReductiveCartanInvolution ((e.symm.trans θ).trans e) ↔ IsReductiveCartanInvolution θ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.conj e⟩
  have heq : ((e.trans ((e.symm.trans θ).trans e)).trans e.symm) = θ := by
    ext x
    simp
  simpa [heq] using h.conj e.symm

end IsReductiveCartanInvolution

/-- Every involutive automorphism of an abelian real Lie algebra is a reductive Cartan
involution. -/
theorem isReductiveCartanInvolution_of_isLieAbelian [IsLieAbelian L] {θ : L ≃ₗ⁅ℝ⁆ L}
    (hinv : ∀ x, θ (θ x) = x) : IsReductiveCartanInvolution θ := by
  refine ⟨hinv, isCartanInvolution_iff.mpr ⟨fun x ↦ Subtype.ext (by simp [hinv]), fun x hx ↦ ?_⟩⟩
  have hbot : derivedSeries ℝ L 1 = ⊥ := by
    rw [derivedSeries_def, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero,
      LieSubmodule.lie_eq_bot_iff]
    intro a _ b _
    exact LieModule.IsTrivial.trivial a b
  exact False.elim (hx (Subtype.ext (by
    have hmem : (x : L) ∈ (⊥ : LieIdeal ℝ L) := hbot ▸ x.property
    exact (LieSubmodule.mem_bot _).mp hmem)))

/-- Assembling an involutive linear equivalence of the centre and a Cartan involution of the
derived ideal produces a reductive Cartan involution. -/
theorem isReductiveCartanInvolution_lieEquivOfIsComplCenterDerived
    (hc : IsCompl (center ℝ L) (derivedSeries ℝ L 1))
    {eZ : center ℝ L ≃ₗ[ℝ] center ℝ L} (heZ : ∀ z, eZ (eZ z) = z)
    {eD : derivedSeries ℝ L 1 ≃ₗ⁅ℝ⁆ derivedSeries ℝ L 1} (heD : IsCartanInvolution eD) :
    IsReductiveCartanInvolution (lieEquivOfIsComplCenterDerived hc eZ eD) := by
  refine ⟨fun x ↦ ?_, ?_⟩
  · have hsup : x ∈ (center ℝ L).toSubmodule ⊔ (derivedSeries ℝ L 1).toSubmodule := by
      rw [(LieSubmodule.isCompl_toSubmodule.mpr hc).sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨z, hz, d, hd, rfl⟩ := Submodule.mem_sup.mp hsup
    rw [map_add, lieEquivOfIsComplCenterDerived_apply_center hc eZ eD ⟨z, hz⟩,
      lieEquivOfIsComplCenterDerived_apply_derivedSeries hc eZ eD ⟨d, hd⟩, map_add,
      lieEquivOfIsComplCenterDerived_apply_center hc eZ eD (eZ ⟨z, hz⟩),
      lieEquivOfIsComplCenterDerived_apply_derivedSeries hc eZ eD (eD ⟨d, hd⟩),
      heZ, heD.apply_apply]
  · simpa using heD

end ReductiveReal

end TauCeti
