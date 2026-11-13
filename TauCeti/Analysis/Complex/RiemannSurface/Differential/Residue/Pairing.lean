/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Germ
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Residue.Basic
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.PrincipalParts
public import TauCeti.Analysis.Meromorphic.ResiduePairing
import TauCeti.Analysis.Meromorphic.PointTwist

/-!
# The residue pairing of principal parts with differentials

Let `X` be a Riemann surface and `D` a divisor on `X`. A Mittag-Leffler distribution
`μ = (μ_x)` relative to `D` (`TauCeti.RiemannSurface.PrincipalParts D`) pairs with a global
section `ω` of `Ω_{-D}`, a meromorphic `1`-form with `div ω ≥ D`, by
`⟨μ, ω⟩ = ∑_x Res_x(φ_x ω)`, where `φ_x` is any meromorphic germ representing `μ_x`
(`TauCeti.RiemannSurface.PrincipalParts.residuePairing`). This does not depend on the
representatives: changing `φ_x` by a germ of order at least `-D x` changes `φ_x ω` by a germ
of order at least `0`, which has residue `0`
(`TauCeti.meromorphicGerms.residue_mul_eq_zero_of_mem_orderGE`).

For the principal parts of a meromorphic function `f` on a compact connected surface, the
pairing is the finite sum of the residues of the meromorphic `1`-form `f ω` over any finite
set containing the poles of `f` and the support of `D`
(`TauCeti.RiemannSurface.PrincipalParts.residuePairing_principalParts`). By the residue theorem
this sum vanishes, which is how the pairing descends to `H¹(X, 𝒪_D) × H⁰(X, Ω_{-D}) → ℂ` in
Serre duality (Forster, §17). The pairing is compatible with the projection
`PrincipalParts D → PrincipalParts E` and the inclusion `Ω_{-E} ⟶ Ω_{-D}` for `D ≤ E`
(`TauCeti.RiemannSurface.PrincipalParts.residuePairing_mapOfLE`).

The local core of the injectivity of the Serre duality map (Forster, Theorem 17.6) is that a
nonzero `ω` pairs nontrivially with a principal part supported at any prescribed point `a` on a
connected surface: if `ω` has order `n` at `a`, the class of the coordinate power `z^(-n-1)`
pairs with `ω` to a nonzero multiple of the leading coefficient of `ω`
(`TauCeti.RiemannSurface.PrincipalParts.residuePairing_single_coordinate_zpow_ne_zero`).

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §17 (the residue pairing `H¹(X, 𝒪_D) × H⁰(X, Ω_{-D}) → ℂ` on Mittag-Leffler distributions).
-/

public noncomputable section

open CategoryTheory Filter OnePoint Opposite Set TopologicalSpace Topology
open scoped Manifold

namespace TauCeti.RiemannSurface

open TauCeti.AlgebraicGeometry (WeilDivisor)

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

namespace differentialSections

variable {D : WeilDivisor X}

/-- The residue of the product of the coordinate germs of a meromorphic function and a section
of `Ω_D` is the residue of the `1`-form `f s`. -/
theorem residue_toChartGerm_mul [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X]
    (f : MeromorphicFunction X) (x : X) (s : differentialSections D ⊤) :
    meromorphicGerms.residue _ (f.toChartGerm x * toChartGerm D x s) =
      (f.finitePart • toOneForm D s).residue x := by
  have hf := (meromorphicAt_def _ _).1 (f.meromorphicAt_finitePart x)
  have hs := (OneForm.meromorphicAt_def _ _).1 (isDifferentialSectionAt_toOneForm s x).meromorphicAt
  have heq : f.toChartGerm x * toChartGerm D x s = meromorphicGerms.mk _ (hf.mul hs) := by
    apply Subtype.ext
    rw [Subring.coe_mul, MeromorphicFunction.coe_toChartGerm, coe_toChartGerm,
      meromorphicGerms.coe_mk, Germ.coe_mul]
  rw [heq, meromorphicGerms.residue_mk, OneForm.residue_def, OneForm.coeff_smul]

end differentialSections

namespace LocalPrincipalPart

variable {D : WeilDivisor X}

variable (D) in
/-- The **local residue pairing** at `x` of principal parts relative to `D` with global sections
of `Ω_{-D}`: the residue at `x` of the product of a representative germ with the coordinate germ
of the `1`-form. It is well defined because a germ of order at least `-D x` times a germ of order
at least `D x` has residue `0`. -/
def residuePairing (x : X) :
    LocalPrincipalPart D x →ₗ[ℂ] differentialSections (-D) ⊤ →ₗ[ℂ] ℂ :=
  (meromorphicGerms.orderGE (chartAt ℂ x x) (-D x)).liftQ
    ((meromorphicGerms.residuePairing (chartAt ℂ x x)).compl₂
      (differentialSections.toChartGerm (-D) x))
    fun φ hφ ↦ LinearMap.mem_ker.2 <| LinearMap.ext fun ω ↦ by
      rw [LinearMap.compl₂_apply, meromorphicGerms.residuePairing_apply, LinearMap.zero_apply]
      exact meromorphicGerms.residue_mul_eq_zero_of_mem_orderGE hφ
        (differentialSections.toChartGerm_mem_orderGE x ω) (by simp)

/-- On representatives, the local residue pairing is the residue of the product of germs. -/
@[simp]
theorem residuePairing_mk (x : X) (φ : meromorphicGerms ℂ (chartAt ℂ x x))
    (ω : differentialSections (-D) ⊤) :
    residuePairing D x (Submodule.Quotient.mk φ) ω =
      meromorphicGerms.residue _ (φ * differentialSections.toChartGerm (-D) x ω) := by
  rw [residuePairing, Submodule.liftQ_apply, LinearMap.compl₂_apply,
    meromorphicGerms.residuePairing_apply]

end LocalPrincipalPart

namespace PrincipalParts

variable {D : WeilDivisor X}

open scoped Classical in
variable (D) in
/-- The **residue pairing** of Mittag-Leffler distributions relative to `D` with global sections
of `Ω_{-D}`: `⟨μ, ω⟩ = ∑_x Res_x(φ_x ω)` for representatives `φ_x` of `μ_x`, a finite sum since
`μ` has finite support. -/
def residuePairing : PrincipalParts D →ₗ[ℂ] differentialSections (-D) ⊤ →ₗ[ℂ] ℂ :=
  DFinsupp.lsum ℕ (LocalPrincipalPart.residuePairing D)

/-- The residue pairing is the sum of the local residue pairings over any finite set outside
which the distribution vanishes. -/
theorem residuePairing_eq_sum (μ : PrincipalParts D) (ω : differentialSections (-D) ⊤)
    (S : Finset X) (hS : ∀ x ∉ S, μ x = 0) :
    residuePairing D μ ω = ∑ x ∈ S, LocalPrincipalPart.residuePairing D x (μ x) ω := by
  classical
  have hsub : μ.support ⊆ S := fun x hx ↦ by
    by_contra h
    exact (DFinsupp.mem_support_iff.1 hx) (hS x h)
  rw [residuePairing, DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply,
    DFinsupp.sum_of_support_subset hsub fun _ _ ↦ map_zero _, LinearMap.sum_apply]
  simp only [LinearMap.toAddMonoidHom_coe]

/-- On a principal part supported at one point, the residue pairing is the local residue
pairing at that point. -/
@[simp]
theorem residuePairing_single [DecidableEq X] (x : X) (m : LocalPrincipalPart D x)
    (ω : differentialSections (-D) ⊤) :
    residuePairing D (DFinsupp.single x m) ω = LocalPrincipalPart.residuePairing D x m ω := by
  rw [residuePairing_eq_sum _ _ {x} fun y hy ↦ DFinsupp.single_eq_of_ne
      (Finset.notMem_singleton.1 hy), Finset.sum_singleton, DFinsupp.single_eq_same]

/-- **The residue pairing on principal parts of a meromorphic function.** On a compact connected
Riemann surface, pairing the principal parts of `f` relative to `D` with `ω ∈ H⁰(X, Ω_{-D})`
gives the sum of the residues of the `1`-form `f ω` over any finite set containing the poles of
`f` and the support of `D`. -/
theorem residuePairing_principalParts [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X] [CompactSpace X]
    (f : MeromorphicFunction X) (ω : differentialSections (-D) ⊤) (S : Finset X)
    (hf : {x | f x = ∞} ⊆ S) (hD : D.support ⊆ S) :
    residuePairing D (f.principalParts D) ω =
      ∑ x ∈ S, (f.finitePart • differentialSections.toOneForm (-D) ω).residue x := by
  rw [residuePairing_eq_sum _ _ S fun x hx ↦ MeromorphicFunction.principalParts_apply_eq_zero
    (fun h ↦ hx (hf h)) (Finsupp.notMem_support_iff.1 fun h ↦ hx (hD h))]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [MeromorphicFunction.principalParts_apply, LocalPrincipalPart.residuePairing_mk,
    differentialSections.residue_toChartGerm_mul]

/-- **Compatibility with increasing the divisor.** For `D ≤ E`, pairing the projection of `μ` to
principal parts relative to `E` with `ω ∈ H⁰(X, Ω_{-E})` is pairing `μ` with the image of `ω`
under the inclusion `Ω_{-E} ⟶ Ω_{-D}`. -/
theorem residuePairing_mapOfLE {E : WeilDivisor X} (h : D ≤ E) (μ : PrincipalParts D)
    (ω : (differentialSheaf (-E)).obj.obj (op ⊤)) :
    residuePairing E (mapOfLE h μ) (differentialSheafSectionsEquiv (-E) ⊤ ω) =
      residuePairing D μ (differentialSheafSectionsEquiv (-D) ⊤
        ((differentialSheafMapOfLE (neg_le_neg h)).hom.app (op ⊤) ω)) := by
  classical
  have hS : ∀ x ∉ μ.support, μ x = 0 := fun x hx ↦ DFinsupp.notMem_support_iff.1 hx
  rw [residuePairing_eq_sum _ _ μ.support fun x hx ↦ by rw [mapOfLE_apply, hS x hx, map_zero],
    residuePairing_eq_sum _ _ μ.support hS]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [mapOfLE_apply]
  induction μ x using Submodule.Quotient.induction_on with
  | _ φ =>
    rw [LocalPrincipalPart.mapOfLE_mk, LocalPrincipalPart.residuePairing_mk,
      LocalPrincipalPart.residuePairing_mk,
      differentialSections.toChartGerm_differentialSheafMapOfLE]

/-- **The local core of Forster 17.6.** If a global section `ω` of `Ω_{-D}` has order `n` at
`a`, it pairs nontrivially with the principal part at `a` of the coordinate power `z^(-n-1)`:
the product has order exactly `-1`. For a section of `Ω_{-D}` one has `n = D a + k` with
`k ≥ 0`, so this is the principal part of `z^(-(D a + k) - 1)`. -/
theorem residuePairing_single_coordinate_zpow_ne_zero [DecidableEq X]
    (ω : differentialSections (-D) ⊤) {a : X} {n : ℤ}
    (hn : (differentialSections.toOneForm (-D) ω).order a = n) :
    residuePairing D (DFinsupp.single a (Submodule.Quotient.mk
      (meromorphicGerms.coordinate (chartAt ℂ a a) ^ (-n - 1)))) ω ≠ 0 := by
  rw [residuePairing_single, LocalPrincipalPart.residuePairing_mk]
  have hmem : differentialSections.toChartGerm (-D) a ω ∈
      meromorphicGerms.orderGE (chartAt ℂ a a) n := by
    rw [meromorphicGerms.mem_orderGE, differentialSections.order_toChartGerm, hn]
  intro h
  have h0 := (meromorphicGerms.coeff_eq_zero_iff n ⟨_, hmem⟩).1
    ((meromorphicGerms.coeff_apply n ⟨_, hmem⟩).trans h)
  rw [meromorphicGerms.mem_orderGE, differentialSections.order_toChartGerm, hn,
    WithTop.coe_le_coe] at h0
  omega

/-- **A nonzero differential pairs nontrivially with principal parts at every point.** On a
connected Riemann surface, a nonzero global section of `Ω_{-D}` pairs nontrivially with some
principal part supported at any prescribed point. -/
theorem exists_residuePairing_single_ne_zero [IsManifold 𝓘(ℂ) 1 X] [PreconnectedSpace X]
    [DecidableEq X]
    {ω : differentialSections (-D) ⊤} (hω : ω ≠ 0) (a : X) :
    ∃ m : LocalPrincipalPart D a, residuePairing D (DFinsupp.single a m) ω ≠ 0 := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1
    (differentialSections.order_toOneForm_ne_top hω a)
  exact ⟨_, residuePairing_single_coordinate_zpow_ne_zero ω hn.symm⟩

end PrincipalParts

end TauCeti.RiemannSurface
