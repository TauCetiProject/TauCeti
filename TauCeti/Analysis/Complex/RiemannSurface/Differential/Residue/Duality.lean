/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Canonical.EulerCharacteristic
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Canonical.Existence
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Cohomology
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Residue.Pairing
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Cohomology.MittagLeffler
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Cohomology.Vanishing
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.RiemannRoch
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Genus
import TauCeti.Analysis.Complex.RiemannSurface.Differential.FiniteDimensional

/-!
# Serre duality on a compact Riemann surface

Let `X` be a compact connected Hausdorff Riemann surface and `D` a divisor on `X`. The residue
pairing `⟨μ, ω⟩ = ∑_x Res_x(μ_x ω)` of Mittag-Leffler distributions `μ` relative to `D` with
global sections `ω` of `Ω_{-D}` (`TauCeti.RiemannSurface.PrincipalParts.residuePairing`) vanishes
on the principal parts of meromorphic functions, by the residue theorem. These are exactly the
distributions killed by the Mittag-Leffler connecting map `PrincipalParts D → H¹(X, 𝒪_D)`
(`TauCeti.RiemannSurface.exact_principalParts_mittagLefflerConnecting`), which is surjective
(Forster, Theorem 17.3, `TauCeti.RiemannSurface.mittagLefflerConnecting_surjective`). So the
pairing descends to the **Serre duality pairing** (`TauCeti.RiemannSurface.serreDualityPairing`)

`H¹(X, 𝒪_D) × H⁰(X, Ω_{-D}) → ℂ`.

A nonzero `ω` pairs nontrivially with a principal part supported at a single point
(`TauCeti.RiemannSurface.PrincipalParts.exists_residuePairing_single_ne_zero`), so the Serre
duality map `H⁰(X, Ω_{-D}) → H¹(X, 𝒪_D)^*` is injective (Forster, Theorem 17.6,
`TauCeti.RiemannSurface.serreDualityMap_injective`).

It is also surjective (Forster, Theorem 17.9, `TauCeti.RiemannSurface.serreDualityMap_surjective`).
A functional `φ` on `H¹(X, 𝒪_D)` is a functional on distributions killing principal parts. If
`φ`, read on distributions relative to a smaller divisor `D'`, is the pairing with a section of
`Ω_{-D'}`, then that section lies in `Ω_{-D}` and represents `φ` (Forster, Lemma 17.8,
`TauCeti.RiemannSurface.exists_residuePairing_flip_eq_of_comp_mapOfLE`). For `B = n [a]` with `n`
large, the functionals `φ ∘ f` for `f ∈ H⁰(X, 𝒪_B)` and the pairings with `Ω_{-(D - B)}` all lie
in the space of functionals relative to `D - B`, whose dimension `h¹(𝒪_{D - B})` is smaller than
`h⁰(𝒪_B) + h⁰(Ω_{-(D - B)})` by Riemann–Roch. So `φ ∘ f` is the pairing with some `ω` for some
`f ≠ 0`, and Lemma 17.8 for `D - B - div f ≤ D` shows that `φ` is the pairing with `ω / f`.

With Riemann–Roch for divisor sheaves, Serre duality gives `h⁰(Ω) = g_an`, `deg K = 2 g_an - 2`
for every canonical divisor `K`, the vanishing of `H¹(X, 𝒪_D)` for `deg D > 2 g_an - 2`, and,
comparing with the topological formula `deg K = -χ(X)`, the equality of the analytic and the
topological genus.

## Main results

* `TauCeti.RiemannSurface.serreDualityPairing`: the Serre duality pairing, with its value on the
  class of a distribution `serreDualityPairing_mittagLefflerConnecting`.
* `TauCeti.RiemannSurface.serreDualityEquiv`: **Serre duality**,
  `H⁰(X, Ω_{-D}) ≃ H¹(X, 𝒪_D)^*`.
* `TauCeti.RiemannSurface.finrank_differentialSections_neg`: `h⁰(Ω_{-D}) = h¹(𝒪_D)`.
* `TauCeti.RiemannSurface.finrank_holomorphicOneForms_eq_analyticGenus`: `h⁰(Ω) = g_an`.
* `TauCeti.RiemannSurface.IsCanonicalDivisor.degree_eq_two_mul_analyticGenus_sub_two`:
  `deg K = 2 g_an - 2`.
* `TauCeti.RiemannSurface.subsingleton_divisorCechCohomology_one_of_degree_gt`: `H¹(X, 𝒪_D) = 0`
  for `deg D > 2 g_an - 2`.
* `TauCeti.RiemannSurface.analyticGenus_eq_genus`: the analytic genus is the topological
  genus, so that `χ(X) = 2 - 2 genus X`
  (`TauCeti.RiemannSurface.eulerChar_eq_two_sub_two_mul_genus`) and `h⁰(Ω) = genus X`
  (`TauCeti.RiemannSurface.finrank_holomorphicOneForms_eq_genus`).

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §17 (Theorem 17.6, injectivity of the duality map, Lemma 17.8, and Theorem 17.9, Serre duality).
-/

public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open TauCeti.Topology
open scoped Manifold

namespace TauCeti.RiemannSurface

open TauCeti.AlgebraicGeometry (WeilDivisor)

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X]
  [T2Space X] [ConnectedSpace X]

section Duality

variable (D : WeilDivisor X)

/-- The residue pairing vanishes on Mittag-Leffler distributions killed by the connecting map:
these are principal parts of meromorphic functions, whose residues add up to zero. -/
theorem ker_mittagLefflerConnecting_le_ker_residuePairing :
    LinearMap.ker (mittagLefflerConnecting D) ≤
      LinearMap.ker (PrincipalParts.residuePairing D) := by
  intro μ hμ
  obtain ⟨f, rfl⟩ := ((exact_principalParts_mittagLefflerConnecting D) μ).1 hμ
  exact LinearMap.mem_ker.2 (LinearMap.ext fun ω ↦
    PrincipalParts.residuePairing_principalParts_eq_zero f ω)

/-- Distributions with the same image under the connecting map have the same residue pairing. -/
theorem residuePairing_eq_of_mittagLefflerConnecting_eq {μ ν : PrincipalParts D}
    (h : mittagLefflerConnecting D μ = mittagLefflerConnecting D ν) :
    PrincipalParts.residuePairing D μ = PrincipalParts.residuePairing D ν := by
  rw [← sub_eq_zero, ← map_sub]
  exact LinearMap.mem_ker.1 (ker_mittagLefflerConnecting_le_ker_residuePairing D
    (LinearMap.mem_ker.2 (by rw [map_sub, h, sub_self])))

/-- **The Serre duality pairing** `H¹(X, 𝒪_D) × H⁰(X, Ω_{-D}) → ℂ`. Every class `ξ` of
`H¹(X, 𝒪_D)` is the Mittag-Leffler obstruction of a distribution `μ` (Forster, Theorem 17.3), and
pairs with `ω` by the residue pairing `⟨μ, ω⟩`, which does not depend on the choice of `μ`
(`TauCeti.RiemannSurface.serreDualityPairing_mittagLefflerConnecting`). -/
def serreDualityPairing :
    divisorCechCohomology D 1 →ₗ[ℂ] differentialSections (-D) ⊤ →ₗ[ℂ] ℂ where
  toFun ξ := PrincipalParts.residuePairing D (mittagLefflerConnecting_surjective D ξ).choose
  map_add' ξ η := by
    rw [← map_add]
    refine residuePairing_eq_of_mittagLefflerConnecting_eq D ?_
    rw [map_add, (mittagLefflerConnecting_surjective D ξ).choose_spec,
      (mittagLefflerConnecting_surjective D η).choose_spec,
      (mittagLefflerConnecting_surjective D (ξ + η)).choose_spec]
  map_smul' c ξ := by
    rw [RingHom.id_apply, ← map_smul]
    refine residuePairing_eq_of_mittagLefflerConnecting_eq D ?_
    rw [map_smul, (mittagLefflerConnecting_surjective D ξ).choose_spec,
      (mittagLefflerConnecting_surjective D (c • ξ)).choose_spec]

/-- The Serre duality pairing of the obstruction of a distribution `μ` is the residue pairing
of `μ`. -/
@[simp]
theorem serreDualityPairing_mittagLefflerConnecting (μ : PrincipalParts D) :
    serreDualityPairing D (mittagLefflerConnecting D μ) = PrincipalParts.residuePairing D μ :=
  residuePairing_eq_of_mittagLefflerConnecting_eq D
    (mittagLefflerConnecting_surjective D _).choose_spec

variable {D} in
/-- **A nonzero section of `Ω_{-D}` pairs nontrivially with some cohomology class**: with the class
of a principal part supported at any single point. -/
theorem exists_serreDualityPairing_ne_zero {ω : differentialSections (-D) ⊤} (hω : ω ≠ 0) :
    ∃ ξ, serreDualityPairing D ξ ω ≠ 0 := by
  classical
  obtain ⟨a⟩ := (inferInstance : Nonempty X)
  obtain ⟨m, hm⟩ := PrincipalParts.exists_residuePairing_single_ne_zero hω a
  exact ⟨mittagLefflerConnecting D (DFinsupp.single a m), by
    rwa [serreDualityPairing_mittagLefflerConnecting]⟩

/-- **The Serre duality map** `H⁰(X, Ω_{-D}) → H¹(X, 𝒪_D)^*`, sending `ω` to the functional
`ξ ↦ ⟨ξ, ω⟩`. -/
def serreDualityMap :
    differentialSections (-D) ⊤ →ₗ[ℂ] Module.Dual ℂ (divisorCechCohomology D 1) :=
  (serreDualityPairing D).flip

@[simp]
theorem serreDualityMap_apply (ω : differentialSections (-D) ⊤) (ξ : divisorCechCohomology D 1) :
    serreDualityMap D ω ξ = serreDualityPairing D ξ ω :=
  (rfl)

/-- **Injectivity of the Serre duality map** (Forster, Theorem 17.6). -/
theorem serreDualityMap_injective : Function.Injective (serreDualityMap D) := by
  refine (injective_iff_map_eq_zero _).2 fun ω hω ↦ by_contra fun hω₀ ↦ ?_
  obtain ⟨ξ, hξ⟩ := exists_serreDualityPairing_ne_zero hω₀
  exact hξ (by rw [← serreDualityMap_apply, hω, LinearMap.zero_apply])

end Duality

/-! ### Surjectivity of the Serre duality map -/

section Surjectivity

variable {D : WeilDivisor X}

/-- A functional on Mittag-Leffler distributions comes from `H¹(X, 𝒪_D)^*` exactly when it kills
the principal parts of meromorphic functions. -/
theorem mem_range_dualMap_mittagLefflerConnecting_iff (φ : Module.Dual ℂ (PrincipalParts D)) :
    φ ∈ LinearMap.range (mittagLefflerConnecting D).dualMap ↔
      φ ∘ₗ MeromorphicFunction.principalParts D = 0 := by
  -- `LinearMap.range_dualMap_eq_dualAnnihilator_ker` needs an `AddCommGroup` instance whose
  -- `AddCommMonoid` is the `DFinsupp.addCommMonoid` used by `mittagLefflerConnecting`. The
  -- instance `DFinsupp.addCommGroup` agrees with it only after unfolding the germ modules, which
  -- are not exposed, and elaboration times out; this instance agrees with it syntactically.
  let := Module.addCommMonoidToAddCommGroup ℂ (M := PrincipalParts D)
  refine ⟨?_, fun h ↦ (LinearMap.range_dualMap_eq_dualAnnihilator_ker _).ge
    ((Submodule.mem_dualAnnihilator _).2 fun μ hμ ↦ ?_)⟩
  · rintro ⟨Λ, rfl⟩
    exact LinearMap.ext fun f ↦ by simp
  obtain ⟨f, rfl⟩ := ((exact_principalParts_mittagLefflerConnecting D) μ).1 hμ
  exact LinearMap.congr_fun h f

/-- The functionals on Mittag-Leffler distributions which kill principal parts form a space of
dimension `h¹(𝒪_D)`. -/
theorem finrank_range_dualMap_mittagLefflerConnecting :
    Module.finrank ℂ (LinearMap.range (mittagLefflerConnecting D).dualMap) =
      Module.finrank ℂ (divisorCechCohomology D 1) :=
  (LinearMap.finrank_range_of_inj (LinearMap.dualMap_injective_of_surjective
    (mittagLefflerConnecting_surjective D))).trans Subspace.dual_finrank_eq

omit [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X] [T2Space X] [ConnectedSpace X] in
/-- **Forster, Lemma 17.8, the order bound.** Let `D' ≤ D` and let `φ` be a functional on
Mittag-Leffler distributions relative to `D`. If `φ`, read on distributions relative to `D'`, is
the residue pairing with `ω ∈ H⁰(X, Ω_{-D'})`, then `ω` has order at least `D x` at every `x`:
otherwise a principal part at `x` which vanishes relative to `D` pairs nontrivially with `ω`. -/
theorem le_order_of_comp_mapOfLE_eq {D' : WeilDivisor X} (h : D' ≤ D)
    {φ : Module.Dual ℂ (PrincipalParts D)} {ω : differentialSections (-D') ⊤}
    (hφ : φ ∘ₗ PrincipalParts.mapOfLE h = (PrincipalParts.residuePairing D').flip ω) (x : X) :
    ((D x : ℤ) : WithTop ℤ) ≤ (differentialSections.toOneForm (-D') ω).order x := by
  classical
  by_contra hlt
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt (not_le.1 hlt))
  rw [← hn, WithTop.coe_le_coe, not_le] at hlt
  set ν : PrincipalParts D' := DFinsupp.single x (Submodule.Quotient.mk
    (meromorphicGerms.coordinate (chartAt ℂ x x) ^ (-n - 1)))
  have hne := PrincipalParts.residuePairing_single_coordinate_zpow_ne_zero ω hn.symm
  have hm : (Submodule.Quotient.mk (meromorphicGerms.coordinate (chartAt ℂ x x) ^ (-n - 1)) :
      LocalPrincipalPart D x) = 0 := by
    rw [Submodule.Quotient.mk_eq_zero, meromorphicGerms.mem_orderGE,
      meromorphicGerms.order_coordinate_zpow, WithTop.coe_le_coe]
    omega
  have hzero : PrincipalParts.mapOfLE h ν = 0 := by
    ext y
    rw [PrincipalParts.mapOfLE_apply, DFinsupp.zero_apply]
    rcases eq_or_ne y x with rfl | hy
    · rw [DFinsupp.single_eq_same, LocalPrincipalPart.mapOfLE_mk, hm]
    · rw [DFinsupp.single_eq_of_ne hy, map_zero]
  have hφν := LinearMap.congr_fun hφ ν
  rw [LinearMap.comp_apply, hzero, map_zero, LinearMap.flip_apply] at hφν
  exact hne hφν.symm

omit [CompactSpace X] [T2Space X] [ConnectedSpace X] in
/-- **Forster, Lemma 17.8.** Let `D' ≤ D` and let `φ` be a functional on Mittag-Leffler
distributions relative to `D`. If `φ`, read on distributions relative to `D'`, is the residue
pairing with a section of `Ω_{-D'}`, then `φ` is the residue pairing with a section of `Ω_{-D}`. -/
theorem exists_residuePairing_flip_eq_of_comp_mapOfLE {D' : WeilDivisor X} (h : D' ≤ D)
    {φ : Module.Dual ℂ (PrincipalParts D)} {ω : differentialSections (-D') ⊤}
    (hφ : φ ∘ₗ PrincipalParts.mapOfLE h = (PrincipalParts.residuePairing D').flip ω) :
    ∃ η, (PrincipalParts.residuePairing D).flip η = φ := by
  have hθ := fun x ↦ (differentialSections.isDifferentialSectionAt_toOneForm ω x).meromorphicAt
  have ho : ∀ x, ((-(-D) x : ℤ) : WithTop ℤ) ≤ (differentialSections.toOneForm (-D') ω).order x :=
    fun x ↦ by simpa only [Finsupp.neg_apply, neg_neg] using le_order_of_comp_mapOfLE_eq h hφ x
  refine ⟨differentialSections.normalize (-D) _ hθ ho, LinearMap.ext fun μ ↦ ?_⟩
  obtain ⟨ν, rfl⟩ := PrincipalParts.mapOfLE_surjective h μ
  rw [LinearMap.flip_apply, ← LinearMap.comp_apply φ, hφ, LinearMap.flip_apply]
  refine PrincipalParts.residuePairing_mapOfLE_of_toChartGerm_eq h ν fun x ↦ ?_
  rw [differentialSections.toChartGerm_eq_mk (hθ x)
    (differentialSections.toOneForm_normalize_eventuallyEq hθ ho x),
    differentialSections.toChartGerm_apply]

omit [T2Space X] in
/-- **Division by a meromorphic function.** Let `f ≠ 0` with `ord f ≥ D₁ - D`. If the composite of
a functional `φ` on Mittag-Leffler distributions relative to `D` with multiplication by `f` is the
residue pairing with a section `ω` of `Ω_{-D₁}`, then `φ` is the residue pairing with a section of
`Ω_{-D}`, namely `ω / f`, by Lemma 17.8 for `D₁ - div f ≤ D`. -/
theorem exists_residuePairing_flip_eq_of_comp_meromorphicMul {D₁ : WeilDivisor X}
    {f : MeromorphicFunction X} (hf₀ : f ≠ 0)
    (hf : ∀ x, ((D₁ x - D x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x f)
    {φ : Module.Dual ℂ (PrincipalParts D)} {ω : differentialSections (-D₁) ⊤}
    (hφ : φ ∘ₗ PrincipalParts.meromorphicMul f hf = (PrincipalParts.residuePairing D₁).flip ω) :
    ∃ η, (PrincipalParts.residuePairing D).flip η = φ := by
  set P := (MeromorphicFunction.orderSystem X).principalDivisor (Additive.ofMul (Units.mk0 f hf₀))
  have hP : ∀ x, MeromorphicFunction.order x f = (P x : WithTop ℤ) :=
    MeromorphicFunction.order_eq_principalDivisor_mk0 hf₀
  have hle : D₁ - P ≤ D := fun x ↦ by
    have := hf x
    rw [hP, WithTop.coe_le_coe] at this
    rw [Finsupp.sub_apply]
    omega
  have hinv : ∀ x, (((D₁ - P) x - D₁ x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x f⁻¹ :=
    fun x ↦ by
      rw [(MeromorphicFunction.order x).map_inv, hP, Finsupp.sub_apply, sub_sub_cancel_left,
        WithTop.LinearOrderedAddCommGroup.coe_neg]
  refine exists_residuePairing_flip_eq_of_comp_mapOfLE hle (ω := differentialSections.meromorphicMul
    f⁻¹ (fun x ↦ by simpa only [Finsupp.neg_apply, neg_sub_neg] using hinv x) ω)
    (LinearMap.ext fun ν ↦ ?_)
  rw [LinearMap.comp_apply, ← PrincipalParts.meromorphicMul_meromorphicMul_eq_mapOfLE hf hinv
    (mul_inv_cancel₀ hf₀), ← LinearMap.comp_apply φ, hφ, LinearMap.flip_apply,
    PrincipalParts.residuePairing_meromorphicMul, LinearMap.flip_apply]

/-- The dimension count behind Forster, Theorem 17.9: for `n` large, with `B = n [a]`,
`h¹(𝒪_{D - B}) < h⁰(𝒪_B) + h⁰(Ω_{-(D - B)})`. -/
private theorem exists_finrank_lt (D : WeilDivisor X) (a : X) :
    ∃ n : ℕ, Module.finrank ℂ (divisorCechCohomology (D - n • WeilDivisor.ofPoint a) 1) <
      Module.finrank ℂ ((divisorSheaf (n • WeilDivisor.ofPoint a)).obj.obj (op ⊤)) +
        Module.finrank ℂ
          ((differentialSheaf (-(D - n • WeilDivisor.ofPoint a))).obj.obj (op ⊤)) := by
  obtain ⟨K, hK⟩ := exists_isCanonicalDivisor (X := X)
  refine ⟨(WeilDivisor.degree D).toNat + 3 * analyticGenus X +
    (-WeilDivisor.degree K).toNat + 1, ?_⟩
  set n : ℕ := (WeilDivisor.degree D).toNat + 3 * analyticGenus X +
    (-WeilDivisor.degree K).toNat + 1
  have hdeg : WeilDivisor.degree (n • WeilDivisor.ofPoint a) = n := by
    rw [map_nsmul, WeilDivisor.degree_ofPoint, nsmul_one]
  have h₁ := finrank_divisorCechCohomology_one_of_degree_neg
    (D := D - n • WeilDivisor.ofPoint a) (by rw [map_sub, hdeg]; omega)
  have h₂ := degree_add_one_sub_analyticGenus_le_finrank_divisorSheaf (n • WeilDivisor.ofPoint a)
  have h₃ := degree_add_one_sub_analyticGenus_le_finrank_divisorSheaf
    (-(D - n • WeilDivisor.ofPoint a) + K)
  rw [← hK.finrank_differentialSections_eq,
    ← (differentialSheafSectionsEquiv _ ⊤).finrank_eq] at h₃
  simp only [map_sub, map_add, map_neg, hdeg] at h₁ h₂ h₃
  omega

/-- **Forster, Theorem 17.9, on Mittag-Leffler distributions.** On a compact connected Hausdorff
Riemann surface, every functional on Mittag-Leffler distributions relative to `D` which kills the
principal parts of meromorphic functions is the residue pairing with a section of `Ω_{-D}`. -/
theorem exists_residuePairing_flip_eq {φ : Module.Dual ℂ (PrincipalParts D)}
    (hφ : φ ∘ₗ MeromorphicFunction.principalParts D = 0) :
    ∃ η, (PrincipalParts.residuePairing D).flip η = φ := by
  obtain ⟨a⟩ := (inferInstance : Nonempty X)
  obtain ⟨n, hn⟩ := exists_finrank_lt D a
  set B := n • WeilDivisor.ofPoint a
  set e := divisorSheafSectionsEquiv B ⊤
  set e' := differentialSheafSectionsEquiv (-(D - B)) ⊤
  have hB : ∀ s, ∀ x, (((D - B) x - D x : ℤ) : WithTop ℤ) ≤
      MeromorphicFunction.order x (divisorSections.toMeromorphic B (e s)) := fun s x ↦ by
    simpa only [Finsupp.sub_apply, sub_sub_cancel_left] using
      divisorSections.neg_le_order_toMeromorphic (e s) x
  -- Multiplying `φ` by `L(B)` and the residue pairing with `Ω_{-(D - B)}` map into the space of
  -- functionals killing principal parts relative to `D - B`, which is too small for both.
  set W := LinearMap.range (mittagLefflerConnecting (D - B)).dualMap
  let α : (divisorSheaf B).obj.obj (op ⊤) →ₗ[ℂ] W :=
    { toFun s := ⟨φ ∘ₗ PrincipalParts.meromorphicMul _ (hB s),
        (mem_range_dualMap_mittagLefflerConnecting_iff _).2 <| LinearMap.ext fun g ↦ by
          rw [LinearMap.comp_apply, LinearMap.comp_apply,
            PrincipalParts.meromorphicMul_principalParts]
          exact LinearMap.congr_fun hφ _⟩
      map_add' s t := Subtype.ext <| (congrArg (φ ∘ₗ ·) (PrincipalParts.meromorphicMul_add
        (hB s) (hB t) (hB (s + t)) (by rw [map_add, map_add]))).trans (LinearMap.comp_add _ _ _)
      map_smul' c s := Subtype.ext <| (congrArg (φ ∘ₗ ·) (PrincipalParts.meromorphicMul_smul c
        (hB s) (hB (c • s)) (by rw [map_smul, map_smul]))).trans (LinearMap.comp_smul _ _ _) }
  let β : (differentialSheaf (-(D - B))).obj.obj (op ⊤) →ₗ[ℂ] W :=
    LinearMap.codRestrict W ((PrincipalParts.residuePairing (D - B)).flip ∘ₗ e'.toLinearMap)
      fun ω ↦ (mem_range_dualMap_mittagLefflerConnecting_iff _).2 <| LinearMap.ext fun g ↦
        PrincipalParts.residuePairing_principalParts_eq_zero g (e' ω)
  obtain ⟨⟨s, ω⟩, hker, hne⟩ : ∃ p ∈ LinearMap.ker (α.coprod β), p ≠ 0 := by
    by_contra! h
    have := LinearMap.finrank_le_finrank_of_injective
      ((injective_iff_map_eq_zero (α.coprod β)).2 fun p hp ↦ h p hp)
    rw [Module.finrank_prod, finrank_range_dualMap_mittagLefflerConnecting] at this
    omega
  have hker' : α s + β ω = 0 := LinearMap.mem_ker.1 hker
  -- By definition of `α` and `β`, the underlying functionals of `α s` and `β ω` are
  -- `φ ∘ₗ meromorphicMul _ (hB s)` and the residue pairing with `e' ω`.
  have hsω : φ ∘ₗ PrincipalParts.meromorphicMul _ (hB s) =
      (PrincipalParts.residuePairing (D - B)).flip (e' (-ω)) :=
    congrArg Subtype.val ((eq_neg_of_add_eq_zero_left hker').trans (map_neg β ω).symm)
  refine exists_residuePairing_flip_eq_of_comp_meromorphicMul (fun h₀ ↦ hne ?_) (hB s) hsω
  have hs : s = 0 := e.map_eq_zero_iff.1
    ((map_eq_zero_iff _ (divisorSections.toMeromorphic_injective B)).1 h₀)
  subst hs
  rw [map_zero, zero_add] at hker'
  have heω : e' ω = 0 := PrincipalParts.residuePairing_flip_injective
    ((congrArg Subtype.val hker').trans (map_zero _).symm)
  exact Prod.ext rfl (e'.map_eq_zero_iff.1 heω)

variable (D)

/-- **Surjectivity of the Serre duality map** (Forster, Theorem 17.9). -/
theorem serreDualityMap_surjective : Function.Surjective (serreDualityMap D) := fun Λ ↦ by
  obtain ⟨ω, hω⟩ := exists_residuePairing_flip_eq (φ := Λ ∘ₗ mittagLefflerConnecting D)
    (LinearMap.ext fun f ↦ by simp)
  refine ⟨ω, LinearMap.ext fun ξ ↦ ?_⟩
  obtain ⟨μ, rfl⟩ := mittagLefflerConnecting_surjective D ξ
  rw [serreDualityMap_apply, serreDualityPairing_mittagLefflerConnecting, ← LinearMap.flip_apply,
    hω, LinearMap.comp_apply]

/-- **Serre duality** (Forster, Theorem 17.9): on a compact connected Hausdorff Riemann surface,
the residue pairing identifies `H⁰(X, Ω_{-D})` with the dual of `H¹(X, 𝒪_D)`. -/
def serreDualityEquiv :
    differentialSections (-D) ⊤ ≃ₗ[ℂ] Module.Dual ℂ (divisorCechCohomology D 1) :=
  LinearEquiv.ofBijective (serreDualityMap D)
    ⟨serreDualityMap_injective D, serreDualityMap_surjective D⟩

@[simp]
theorem serreDualityEquiv_apply (ω : differentialSections (-D) ⊤) :
    serreDualityEquiv D ω = serreDualityMap D ω :=
  (rfl)

/-- **`h⁰(Ω_{-D}) = h¹(𝒪_D)`.** -/
theorem finrank_differentialSections_neg :
    Module.finrank ℂ (differentialSections (-D) ⊤) =
      Module.finrank ℂ (divisorCechCohomology D 1) :=
  (serreDualityEquiv D).finrank_eq.trans (Subspace.dual_finrank_eq (K := ℂ))

/-- **`h¹(𝒪_D) = h⁰(𝒪_{K - D})`** for every canonical divisor `K`. -/
theorem IsCanonicalDivisor.finrank_divisorCechCohomology_one_eq {K : WeilDivisor X}
    (hK : IsCanonicalDivisor K) :
    Module.finrank ℂ (divisorCechCohomology D 1) =
      Module.finrank ℂ ((divisorSheaf (K - D)).obj.obj (op ⊤)) := by
  rw [← finrank_differentialSections_neg, hK.finrank_differentialSections_eq, neg_add_eq_sub]

end Surjectivity

section AnalyticGenus

/-- **`h⁰(Ω) = g_an`.** On a compact connected Hausdorff Riemann surface, the holomorphic
`1`-forms have dimension the analytic genus. -/
theorem finrank_holomorphicOneForms_eq_analyticGenus :
    Module.finrank ℂ (holomorphicOneForms X) = analyticGenus X := by
  have h := finrank_differentialSections_neg (0 : WeilDivisor X)
  rw [neg_zero, differentialSectionsZeroEquiv.finrank_eq] at h
  rwa [analyticGenus_eq_finrank_divisorCechCohomology]

/-- **`deg K = 2 g_an - 2`.** On a compact connected Hausdorff Riemann surface, every canonical
divisor `K` has degree `2 g_an - 2`. -/
theorem IsCanonicalDivisor.degree_eq_two_mul_analyticGenus_sub_two {K : WeilDivisor X}
    (hK : IsCanonicalDivisor K) : WeilDivisor.degree K = 2 * analyticGenus X - 2 := by
  -- `h⁰(K) = h¹(𝒪) = g_an` and `h¹(K) = h⁰(𝒪) = 1`.
  have h₀ := hK.finrank_divisorCechCohomology_one_eq 0
  rw [sub_zero, ← analyticGenus_eq_finrank_divisorCechCohomology] at h₀
  have h₁ := hK.finrank_divisorCechCohomology_one_eq K
  rw [sub_self, finrank_divisorSheaf_zero] at h₁
  have hRR := finrank_divisorSheaf_euler_characteristic K
  omega

/-- **Vanishing of `H¹`.** On a compact connected Hausdorff Riemann surface, `H¹(X, 𝒪_D) = 0` for
every divisor `D` of degree `deg D > 2 g_an - 2`. -/
theorem subsingleton_divisorCechCohomology_one_of_degree_gt {D : WeilDivisor X}
    (hD : 2 * (analyticGenus X : ℤ) - 2 < WeilDivisor.degree D) :
    Subsingleton (divisorCechCohomology D 1) := by
  obtain ⟨K, hK⟩ := exists_isCanonicalDivisor (X := X)
  refine Module.finrank_zero_iff (R := ℂ).1 ?_
  rw [hK.finrank_divisorCechCohomology_one_eq]
  refine finrank_divisorSheaf_eq_zero_of_degree_neg ?_
  rw [map_sub, hK.degree_eq_two_mul_analyticGenus_sub_two]
  omega

/-- **The analytic genus is the topological genus.** On a compact connected Hausdorff Riemann
surface, `g_an = genus X`, from `deg K = 2 g_an - 2` and `deg K = -χ(X)` for a canonical
divisor `K`. -/
theorem analyticGenus_eq_genus : analyticGenus X = genus X := by
  obtain ⟨K, hK⟩ := exists_isCanonicalDivisor (X := X)
  have h := hK.degree_eq_two_mul_analyticGenus_sub_two
  rw [hK.degree_eq_neg_eulerChar] at h
  rw [genus_def]
  omega

/-- **`χ = 2 - 2g`.** A compact connected Hausdorff Riemann surface has Euler characteristic
`2 - 2 genus X`, since a canonical divisor has degree `-χ(X) = 2 g_an - 2`. -/
theorem eulerChar_eq_two_sub_two_mul_genus : eulerChar X = 2 - 2 * genus X := by
  obtain ⟨K, hK⟩ := exists_isCanonicalDivisor (X := X)
  have h := hK.degree_eq_two_mul_analyticGenus_sub_two
  rw [hK.degree_eq_neg_eulerChar, analyticGenus_eq_genus] at h
  omega

/-- **`h⁰(Ω) = g`.** On a compact connected Hausdorff Riemann surface, the holomorphic `1`-forms
have dimension the topological genus. -/
theorem finrank_holomorphicOneForms_eq_genus :
    Module.finrank ℂ (holomorphicOneForms X) = genus X := by
  rw [finrank_holomorphicOneForms_eq_analyticGenus, analyticGenus_eq_genus]

end AnalyticGenus

end TauCeti.RiemannSurface

