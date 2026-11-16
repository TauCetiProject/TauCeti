/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Prod
public import Mathlib.Algebra.Lie.Solvable
import Mathlib.LinearAlgebra.Projection
import TauCeti.Algebra.Lie.Prod

/-!
# Restrictions and centre/derived assembly of Lie algebra equivalences

Every Lie algebra equivalence `e : L ≃ₗ⁅R⁆ M` carries the centre `Z(L)` onto `Z(M)`
(`LieEquiv.map_center`) and each term of the derived series onto the corresponding term of `M`
(`LieEquiv.map_derivedSeries`), inducing equivalences `LieEquiv.restrictCenter` and
`LieEquiv.restrictDerivedSeries`.

When `L` splits as the direct sum of its centre and its derived ideal,
`IsCompl (center R L) (derivedSeries R L 1)`, addition yields a Lie algebra isomorphism
`Z(L) × [L, L] ≃ₗ⁅R⁆ L` (`LieEquiv.prodCenterDerivedEquiv`), and any pair of automorphisms of
`Z(L)` and `[L, L]` assembles into an automorphism of `L` (`LieEquiv.ofCenterDerived`) whose
restrictions recover the two factors.

## Main definitions

* `LieEquiv.restrictCenter` and `LieEquiv.restrictDerivedSeries`: restriction of a Lie algebra
  equivalence to the centre and to any term of the derived series.
* `LieEquiv.prodCenterDerivedEquiv`: the Lie isomorphism `Z(L) × [L, L] ≃ₗ⁅R⁆ L` when the centre
  and derived ideal are complementary.
* `LieEquiv.ofCenterDerived`: assembly of automorphisms of `Z(L)` and `[L, L]` into an automorphism
  of `L`.

## Main results

* `LieEquiv.map_center` and `LieEquiv.map_derivedSeries`: invariance of the centre and derived
  series under Lie algebra equivalences.
* `LieEquiv.restrictCenter_ofCenterDerived` and `LieEquiv.restrictDerivedSeries_ofCenterDerived`:
  restricting an assembled automorphism recovers the central and derived factors.
-/

public section

open LieAlgebra

namespace LieEquiv

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

/-- Every Lie algebra equivalence maps the centre onto the centre. -/
theorem map_center (e : L ≃ₗ⁅R⁆ M) :
    (center R L).toLieSubalgebra.map e.toLieHom = (center R M).toLieSubalgebra := by
  ext y
  rw [LieSubalgebra.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [LieIdeal.mem_toLieSubalgebra, LieModule.mem_maxTrivSubmodule]
    intro w
    obtain ⟨u, rfl⟩ := e.surjective w
    rw [coe_toLieHom, ← e.map_lie, (LieModule.mem_maxTrivSubmodule R L L x).mp hx u, map_zero]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [LieIdeal.mem_toLieSubalgebra, LieModule.mem_maxTrivSubmodule]
    intro u
    apply e.injective
    rw [e.toLieHom.map_lie, map_zero, coe_toLieHom, e.apply_symm_apply]
    exact (LieModule.mem_maxTrivSubmodule R M M y).mp hy (e u)

/-- Restriction of a Lie algebra equivalence to the centre. -/
def restrictCenter (e : L ≃ₗ⁅R⁆ M) : center R L ≃ₗ⁅R⁆ center R M :=
  e.ofSubalgebras (center R L).toLieSubalgebra (center R M).toLieSubalgebra e.map_center

@[simp, grind =]
theorem coe_restrictCenter (e : L ≃ₗ⁅R⁆ M) (z : center R L) :
    (e.restrictCenter z : M) = e z := by
  exact e.ofSubalgebras_apply _ _ e.map_center z

@[simp, grind =]
theorem coe_restrictCenter_symm (e : L ≃ₗ⁅R⁆ M) (z : center R M) :
    (e.restrictCenter.symm z : L) = e.symm z := by
  exact e.ofSubalgebras_symm_apply _ _ e.map_center z

/-- Restricting the inverse equivalence to the centre equals the inverse of the restriction. -/
@[simp]
theorem restrictCenter_symm (e : L ≃ₗ⁅R⁆ M) :
    e.symm.restrictCenter = e.restrictCenter.symm := by
  ext z
  simp

/-- Restricting a composite equivalence to the centre composes the restrictions. -/
theorem restrictCenter_trans {N : Type*} [LieRing N] [LieAlgebra R N]
    (e₁ : L ≃ₗ⁅R⁆ M) (e₂ : M ≃ₗ⁅R⁆ N) :
    (e₁.trans e₂).restrictCenter = e₁.restrictCenter.trans e₂.restrictCenter := by
  ext z
  simp

/-- Every Lie algebra equivalence maps each term of the derived series onto the corresponding term
of the target. -/
theorem map_derivedSeries (e : L ≃ₗ⁅R⁆ M) (k : ℕ) :
    (derivedSeries R L k).toLieSubalgebra.map e.toLieHom =
      (derivedSeries R M k).toLieSubalgebra := by
  ext y
  rw [LieSubalgebra.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (LieIdeal.derivedSeries_map_le (f := e.toLieHom) k) (LieIdeal.mem_map hx)
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    exact (LieIdeal.derivedSeries_map_le (f := e.symm.toLieHom) k) (LieIdeal.mem_map hy)

/-- Restriction of a Lie algebra equivalence to the `k`-th term of the derived series. -/
def restrictDerivedSeries (e : L ≃ₗ⁅R⁆ M) (k : ℕ) :
    derivedSeries R L k ≃ₗ⁅R⁆ derivedSeries R M k :=
  e.ofSubalgebras (derivedSeries R L k).toLieSubalgebra (derivedSeries R M k).toLieSubalgebra
    (e.map_derivedSeries k)

@[simp, grind =]
theorem coe_restrictDerivedSeries (e : L ≃ₗ⁅R⁆ M) (k : ℕ) (x : derivedSeries R L k) :
    (e.restrictDerivedSeries k x : M) = e x := by
  exact e.ofSubalgebras_apply _ _ (e.map_derivedSeries k) x

@[simp, grind =]
theorem coe_restrictDerivedSeries_symm (e : L ≃ₗ⁅R⁆ M) (k : ℕ) (y : derivedSeries R M k) :
    ((e.restrictDerivedSeries k).symm y : L) = e.symm y := by
  exact e.ofSubalgebras_symm_apply _ _ (e.map_derivedSeries k) y

/-- Restricting the inverse equivalence to a derived-series term equals the inverse of the
restriction. -/
@[simp]
theorem restrictDerivedSeries_symm (e : L ≃ₗ⁅R⁆ M) (k : ℕ) :
    e.symm.restrictDerivedSeries k = (e.restrictDerivedSeries k).symm := by
  ext x
  simp

/-- Restricting a composite equivalence to a term of the derived series composes the
restrictions. -/
theorem restrictDerivedSeries_trans {N : Type*} [LieRing N] [LieAlgebra R N]
    (e₁ : L ≃ₗ⁅R⁆ M) (e₂ : M ≃ₗ⁅R⁆ N) (k : ℕ) :
    (e₁.trans e₂).restrictDerivedSeries k =
      (e₁.restrictDerivedSeries k).trans (e₂.restrictDerivedSeries k) := by
  ext x
  simp

/-- When the centre and derived ideal of `L` are complementary, addition gives a Lie algebra
equivalence `Z(L) × [L, L] ≃ₗ⁅R⁆ L`. -/
noncomputable def prodCenterDerivedEquiv
    (hcompl : IsCompl (center R L) (derivedSeries R L 1)) :
    (center R L × derivedSeries R L 1) ≃ₗ⁅R⁆ L where
  __ := Submodule.prodEquivOfIsCompl (center R L).toSubmodule (derivedSeries R L 1).toSubmodule
    (LieSubmodule.isCompl_toSubmodule.mpr hcompl)
  map_lie' {p q} := by
    have hz (z : center R L) (y : L) : ⁅y, (z : L)⁆ = 0 :=
      (LieModule.mem_maxTrivSubmodule R L L z).mp z.property y
    have hzl (z : center R L) (y : L) : ⁅(z : L), y⁆ = 0 := by
      rw [← lie_skew, hz z y, neg_zero]
    have h1 : ((⁅p.1, q.1⁆ : center R L) : L) = ⁅(p.1 : L), (q.1 : L)⁆ := rfl
    have h2 : ((⁅p.2, q.2⁆ : derivedSeries R L 1) : L) = ⁅(p.2 : L), (q.2 : L)⁆ := rfl
    simp only [LinearEquiv.toFun_eq_coe, Submodule.coe_prodEquivOfIsCompl',
      LieAlgebra.Prod.bracket_apply, h1, h2, lie_add, add_lie, hz, hzl, zero_add]

@[simp, grind =]
theorem prodCenterDerivedEquiv_apply
    (hcompl : IsCompl (center R L) (derivedSeries R L 1))
    (p : center R L × derivedSeries R L 1) :
    prodCenterDerivedEquiv hcompl p = (p.1 : L) + p.2 :=
  (rfl)

@[simp]
theorem prodCenterDerivedEquiv_symm_center
    (hcompl : IsCompl (center R L) (derivedSeries R L 1)) (z : center R L) :
    (prodCenterDerivedEquiv hcompl).symm (z : L) = (z, 0) := by
  apply (prodCenterDerivedEquiv hcompl).injective
  simp

@[simp]
theorem prodCenterDerivedEquiv_symm_derivedSeries
    (hcompl : IsCompl (center R L) (derivedSeries R L 1)) (d : derivedSeries R L 1) :
    (prodCenterDerivedEquiv hcompl).symm (d : L) = (0, d) := by
  apply (prodCenterDerivedEquiv hcompl).injective
  simp

/-- Assemble automorphisms of `Z(L)` and `[L, L]` into an automorphism of `L` when the centre and
derived ideal are complementary. -/
noncomputable def ofCenterDerived
    (hcompl : IsCompl (center R L) (derivedSeries R L 1))
    (θZ : center R L ≃ₗ⁅R⁆ center R L)
    (θD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) :
    L ≃ₗ⁅R⁆ L :=
  (prodCenterDerivedEquiv hcompl).symm.trans
    ((LieEquiv.prodCongr θZ θD).trans (prodCenterDerivedEquiv hcompl))

@[simp]
theorem ofCenterDerived_apply_center
    (hcompl : IsCompl (center R L) (derivedSeries R L 1))
    (θZ : center R L ≃ₗ⁅R⁆ center R L)
    (θD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1)
    (z : center R L) :
    ofCenterDerived hcompl θZ θD (z : L) = θZ z := by
  simp [ofCenterDerived]

@[simp]
theorem ofCenterDerived_apply_derivedSeries
    (hcompl : IsCompl (center R L) (derivedSeries R L 1))
    (θZ : center R L ≃ₗ⁅R⁆ center R L)
    (θD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1)
    (d : derivedSeries R L 1) :
    ofCenterDerived hcompl θZ θD (d : L) = θD d := by
  simp [ofCenterDerived]

@[simp]
theorem restrictCenter_ofCenterDerived
    (hcompl : IsCompl (center R L) (derivedSeries R L 1))
    (θZ : center R L ≃ₗ⁅R⁆ center R L)
    (θD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) :
    (ofCenterDerived hcompl θZ θD).restrictCenter = θZ := by
  ext z
  simp

@[simp]
theorem restrictDerivedSeries_ofCenterDerived
    (hcompl : IsCompl (center R L) (derivedSeries R L 1))
    (θZ : center R L ≃ₗ⁅R⁆ center R L)
    (θD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) :
    (ofCenterDerived hcompl θZ θD).restrictDerivedSeries 1 = θD := by
  ext d
  simp

@[simp]
theorem ofCenterDerived_symm
    (hcompl : IsCompl (center R L) (derivedSeries R L 1))
    (θZ : center R L ≃ₗ⁅R⁆ center R L)
    (θD : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) :
    (ofCenterDerived hcompl θZ θD).symm = ofCenterDerived hcompl θZ.symm θD.symm := by
  ext x
  obtain ⟨⟨z, d⟩, rfl⟩ := (prodCenterDerivedEquiv hcompl).surjective x
  rw [symm_apply_eq]
  simp [map_add]

end LieEquiv
