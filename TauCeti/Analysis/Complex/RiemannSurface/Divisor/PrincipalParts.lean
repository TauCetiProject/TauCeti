/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Meromorphic
public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Germ
public import TauCeti.Analysis.Meromorphic.OrderFiltration
public import Mathlib.LinearAlgebra.DFinsupp
import TauCeti.Data.DFinsupp.Basic

/-!
# Mittag-Leffler principal parts relative to a divisor

Let `X` be a Riemann surface and `D` a divisor on `X`. A *principal part relative to `D`* at a
point `x` is a meromorphic germ at `x`, read in the preferred chart at `x`, modulo the germs of
order at least `-D x`, that is, modulo the stalk of `𝒪_D` at `x`
(`TauCeti.RiemannSurface.LocalPrincipalPart`). A *Mittag-Leffler distribution* relative to `D`
is a family of such local principal parts, almost all zero
(`TauCeti.RiemannSurface.PrincipalParts`). For `D = 0` these are Forster's Mittag-Leffler
distributions: a local principal part is a Laurent tail `∑_{k < 0} c_k z^k`.

On a compact connected Riemann surface, a meromorphic function `f` has a principal part at
every point, nonzero only at the finitely many poles of `f` and points of the support of `D`
(`TauCeti.RiemannSurface.MeromorphicFunction.principalParts`). The functions with zero
principal parts are exactly the global sections of `𝒪_D`
(`TauCeti.RiemannSurface.MeromorphicFunction.ker_principalParts`), so that
`0 → H⁰(X, 𝒪_D) → 𝓜(X) → PrincipalParts D` is exact. The cokernel of the second map is
`H¹(X, 𝒪_D)` (Forster, Theorem 17.3), which is how the residue pairing of principal parts with
differentials descends to Serre duality.

For `D ≤ E` there is a surjection `PrincipalParts D → PrincipalParts E`
(`TauCeti.RiemannSurface.PrincipalParts.mapOfLE`), compatible with taking principal parts of
meromorphic functions. Its kernel at `x` consists of the principal parts with poles bounded by
`E` (`TauCeti.RiemannSurface.LocalPrincipalPart.boundedBy`): the classes of germs of order at
least `-E x`.

On a connected surface, a meromorphic function `f` with `ord f ≥ D - E` multiplies Mittag-Leffler
distributions relative to `D` into those relative to `E`
(`TauCeti.RiemannSurface.PrincipalParts.meromorphicMul`), compatibly with taking principal parts
(`TauCeti.RiemannSurface.PrincipalParts.meromorphicMul_principalParts`).

Every local principal part `p` relative to `D` has a least pole bound
`TauCeti.RiemannSurface.LocalPrincipalPart.poleBound D p ≥ D x`, and every Mittag-Leffler
distribution `μ` a least bounding divisor
`TauCeti.RiemannSurface.PrincipalParts.boundingDivisor μ` built from them. The distributions
bounded by `E` (`TauCeti.RiemannSurface.PrincipalParts.boundedBy`) are the same as families of
local principal parts bounded by `E` (`TauCeti.RiemannSurface.PrincipalParts.toBoundedFamily`).

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §§16-18 (Mittag-Leffler distributions and the residue pairing).
-/

public noncomputable section

open Filter OnePoint Set Topology
open scoped Manifold

namespace TauCeti.RiemannSurface

open TauCeti.AlgebraicGeometry (WeilDivisor)

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- A **local principal part relative to `D`** at `x`: a meromorphic germ at `x`, in the
preferred chart at `x`, modulo the germs of order at least `-D x`. -/
abbrev LocalPrincipalPart (D : WeilDivisor X) (x : X) : Type :=
  meromorphicGerms ℂ (chartAt ℂ x x) ⧸ meromorphicGerms.orderGE (chartAt ℂ x x) (-D x)

/-- The **Mittag-Leffler distributions relative to `D`**: families of local principal parts
relative to `D`, almost all of which are zero. -/
abbrev PrincipalParts (D : WeilDivisor X) : Type _ :=
  Π₀ x, LocalPrincipalPart D x

namespace LocalPrincipalPart

variable {D E : WeilDivisor X}

/-- For `D ≤ E`, the projection of local principal parts relative to `D` onto those relative
to `E`: the germs of order at least `-D x` have order at least `-E x`. -/
def mapOfLE (h : D ≤ E) (x : X) : LocalPrincipalPart D x →ₗ[ℂ] LocalPrincipalPart E x :=
  Submodule.factor (meromorphicGerms.orderGE_antitone _ (neg_le_neg (h x)))

@[simp]
theorem mapOfLE_mk (h : D ≤ E) (x : X) (φ : meromorphicGerms ℂ (chartAt ℂ x x)) :
    mapOfLE h x (Submodule.Quotient.mk φ) = Submodule.Quotient.mk φ :=
  (rfl)

theorem mapOfLE_surjective (h : D ≤ E) (x : X) : Function.Surjective (mapOfLE h x) :=
  Submodule.factor_surjective (meromorphicGerms.orderGE_antitone _ (neg_le_neg (h x)))

variable (D E) in
/-- The **principal parts relative to `D` with poles bounded by `E`** at `x`: the classes of the
coordinate germs of order at least `-E x`, modulo those of order at least `-D x`. For `D ≤ E` it
is the kernel of the projection `LocalPrincipalPart D x → LocalPrincipalPart E x`. -/
def boundedBy (x : X) : Submodule ℂ (LocalPrincipalPart D x) :=
  (meromorphicGerms.orderGE (chartAt ℂ x x) (-E x)).map
    (meromorphicGerms.orderGE (chartAt ℂ x x) (-D x)).mkQ

variable {x : X}

/-- A principal part is bounded by `E` exactly when it is the class of a germ satisfying the
order bound of `E`. -/
theorem mem_boundedBy_iff {p : LocalPrincipalPart D x} :
    p ∈ boundedBy D E x ↔
      ∃ φ ∈ meromorphicGerms.orderGE (chartAt ℂ x x) (-E x), Submodule.Quotient.mk φ = p :=
  Submodule.mem_map

/-- The class of a germ satisfying the order bound of `E` is bounded by `E`. -/
theorem mk_mem_boundedBy {φ : meromorphicGerms ℂ (chartAt ℂ x x)}
    (hφ : φ ∈ meromorphicGerms.orderGE (chartAt ℂ x x) (-E x)) :
    (Submodule.Quotient.mk φ : LocalPrincipalPart D x) ∈ boundedBy D E x :=
  Submodule.mem_map_of_mem hφ

/-- Where `E` permits no more poles than `D`, there are no principal parts bounded by `E`. -/
theorem boundedBy_eq_bot (h : E x ≤ D x) : boundedBy D E x = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨φ, hφ, rfl⟩
  exact (Submodule.mem_bot ℂ).2 ((Submodule.Quotient.mk_eq_zero _).2
    (meromorphicGerms.orderGE_antitone _ (neg_le_neg h) hφ))

/-- For `D ≤ E`, the principal parts bounded by `E` are those which vanish relative to `E`. -/
theorem boundedBy_eq_ker_mapOfLE (h : D ≤ E) (x : X) :
    boundedBy D E x = LinearMap.ker (mapOfLE h x) := by
  have he :
      mapOfLE h x = Submodule.factor (meromorphicGerms.orderGE_antitone _ (neg_le_neg (h x))) :=
    Submodule.linearMap_qext _ (LinearMap.ext (mapOfLE_mk h x))
  rw [he, Submodule.ker_mapQ, Submodule.comap_id]
  rfl

variable {D' E' : WeilDivisor X}

/-- Principal parts bounded by `E` are bounded by every `E'` permitting more poles at `x`. -/
theorem boundedBy_mono (h : E x ≤ E' x) : boundedBy D E x ≤ boundedBy D E' x := fun _ hp ↦ by
  obtain ⟨φ, hφ, rfl⟩ := mem_boundedBy_iff.1 hp
  exact mk_mem_boundedBy (meromorphicGerms.orderGE_antitone _ (neg_le_neg h) hφ)

/-- The projection to a larger divisor `D'` maps principal parts bounded by `E` to principal parts
bounded by every `E'` permitting more poles at `x`. -/
theorem mapOfLE_mem_boundedBy (hD : D ≤ D') (hE : E x ≤ E' x) {p : LocalPrincipalPart D x}
    (hp : p ∈ boundedBy D E x) : mapOfLE hD x p ∈ boundedBy D' E' x := by
  obtain ⟨φ, hφ, rfl⟩ := mem_boundedBy_iff.1 hp
  rw [mapOfLE_mk]
  exact mk_mem_boundedBy (meromorphicGerms.orderGE_antitone _ (neg_le_neg hE) hφ)

@[simp]
theorem mapOfLE_refl_apply (p : LocalPrincipalPart D x) : mapOfLE (le_refl D) x p = p := by
  induction p using Submodule.Quotient.induction_on with
  | _ φ => rw [mapOfLE_mk]

/-- For `D ≤ D'` and `E x ≤ E' x`, the projection `LocalPrincipalPart.mapOfLE` restricted to the
principal parts bounded by `E` and `E'`. -/
def boundedByMapOfLE (hD : D ≤ D') (hE : E x ≤ E' x) :
    boundedBy D E x →ₗ[ℂ] boundedBy D' E' x :=
  (mapOfLE hD x).restrict fun _ ↦ mapOfLE_mem_boundedBy hD hE

@[simp]
theorem coe_boundedByMapOfLE_apply (hD : D ≤ D') (hE : E x ≤ E' x) (p : boundedBy D E x) :
    (boundedByMapOfLE hD hE p : LocalPrincipalPart D' x) = mapOfLE hD x p := (rfl)

/-- A principal part relative to `D` at `x` whose poles are bounded by the integer `n`. -/
private def BoundedAt (p : LocalPrincipalPart D x) (n : ℤ) : Prop :=
  ∃ φ ∈ meromorphicGerms.orderGE (chartAt ℂ x x) (-n), Submodule.Quotient.mk φ = p

/-- Every local principal part has some pole bound. -/
private theorem exists_boundedAt (p : LocalPrincipalPart D x) :
    ∃ n, D x ≤ n ∧ BoundedAt p n := by
  induction p using Submodule.Quotient.induction_on with
  | _ φ =>
    cases h : meromorphicGerms.order φ with
    | top =>
      refine ⟨D x, le_rfl, φ, ?_, rfl⟩
      rw [meromorphicGerms.mem_orderGE, h]
      exact le_top
    | coe m =>
      refine ⟨max (D x) (-m), le_max_left _ _, φ, ?_, rfl⟩
      rw [meromorphicGerms.mem_orderGE, h, WithTop.coe_le_coe]
      have := le_max_right (D x) (-m)
      omega

variable (D) in
/-- The **pole bound** of a local principal part relative to `D` at `x`: the least integer
`n ≥ D x` such that the principal part is the class of a germ of order at least `-n`. -/
def poleBound (p : LocalPrincipalPart D x) : ℤ :=
  sInf {n | D x ≤ n ∧ BoundedAt p n}

private theorem poleBound_mem (p : LocalPrincipalPart D x) :
    poleBound D p ∈ {n | D x ≤ n ∧ BoundedAt p n} :=
  Int.csInf_mem (exists_boundedAt p) ⟨D x, fun _ hn ↦ hn.1⟩

theorem le_poleBound (p : LocalPrincipalPart D x) : D x ≤ poleBound D p :=
  (poleBound_mem p).1

/-- A principal part is bounded by every divisor whose coefficient at `x` is at least its pole
bound. -/
theorem mem_boundedBy_of_poleBound_le {p : LocalPrincipalPart D x} (h : poleBound D p ≤ E x) :
    p ∈ boundedBy D E x := by
  obtain ⟨φ, hφ, rfl⟩ := (poleBound_mem p).2
  exact mk_mem_boundedBy (meromorphicGerms.orderGE_antitone _ (neg_le_neg h) hφ)

/-- The pole bound is least among the bounds `E x ≥ D x`. -/
theorem poleBound_le {p : LocalPrincipalPart D x} (hD : D x ≤ E x) (hp : p ∈ boundedBy D E x) :
    poleBound D p ≤ E x :=
  csInf_le ⟨D x, fun _ hn ↦ hn.1⟩ ⟨hD, mem_boundedBy_iff.1 hp⟩

/-- A principal part is bounded by `E` with `E x ≥ D x` exactly when its pole bound is at most
`E x`. -/
theorem mem_boundedBy_iff_poleBound_le {p : LocalPrincipalPart D x} (hD : D x ≤ E x) :
    p ∈ boundedBy D E x ↔ poleBound D p ≤ E x :=
  ⟨poleBound_le hD, mem_boundedBy_of_poleBound_le⟩

@[simp]
theorem poleBound_zero : poleBound D (0 : LocalPrincipalPart D x) = D x :=
  le_antisymm (csInf_le ⟨D x, fun _ hn ↦ hn.1⟩ ⟨le_rfl, 0, Submodule.zero_mem _, rfl⟩)
    (le_poleBound _)

end LocalPrincipalPart

namespace PrincipalParts

variable {D E F : WeilDivisor X}

/-- For `D ≤ E`, the projection of Mittag-Leffler distributions relative to `D` onto those
relative to `E`, pointwise by `TauCeti.RiemannSurface.LocalPrincipalPart.mapOfLE`. -/
def mapOfLE (h : D ≤ E) : PrincipalParts D →ₗ[ℂ] PrincipalParts E :=
  DFinsupp.mapRange.linearMap fun x ↦ LocalPrincipalPart.mapOfLE h x

@[simp]
theorem mapOfLE_apply (h : D ≤ E) (μ : PrincipalParts D) (x : X) :
    mapOfLE h μ x = LocalPrincipalPart.mapOfLE h x (μ x) :=
  (rfl)

/-- The projection of Mittag-Leffler distributions to a larger divisor is surjective. -/
theorem mapOfLE_surjective (h : D ≤ E) : Function.Surjective (mapOfLE h) :=
  (DFinsupp.mapRange_surjective _ fun _ ↦ map_zero _).2 fun x ↦
    LocalPrincipalPart.mapOfLE_surjective h x

@[simp]
theorem mapOfLE_refl : mapOfLE (le_refl D) = LinearMap.id := by
  ext μ x : 2
  rw [mapOfLE_apply, LinearMap.id_apply, LocalPrincipalPart.mapOfLE_refl_apply]

@[simp]
theorem mapOfLE_comp (hDE : D ≤ E) (hEF : E ≤ F) :
    (mapOfLE hEF).comp (mapOfLE hDE) = mapOfLE (hDE.trans hEF) := by
  ext μ x : 2
  simp only [LinearMap.comp_apply, mapOfLE_apply]
  induction μ x using Submodule.Quotient.induction_on with
  | _ φ => simp only [LocalPrincipalPart.mapOfLE_mk]

section Bounds

variable {D' E' : WeilDivisor X}

variable (D E) in
/-- The **Mittag-Leffler distributions relative to `D` with poles bounded by `E`**: those whose
local principal parts all lie in `LocalPrincipalPart.boundedBy D E x`. -/
def boundedBy : Submodule ℂ (PrincipalParts D) :=
  ⨅ x, (LocalPrincipalPart.boundedBy D E x).comap (DFinsupp.lapply x)

@[simp]
theorem mem_boundedBy_iff {μ : PrincipalParts D} :
    μ ∈ boundedBy D E ↔ ∀ x, μ x ∈ LocalPrincipalPart.boundedBy D E x := by
  simp only [boundedBy, Submodule.mem_iInf, Submodule.mem_comap, DFinsupp.lapply_apply]

theorem boundedBy_mono (h : E ≤ E') : boundedBy D E ≤ boundedBy D E' := fun _ hμ ↦
  mem_boundedBy_iff.2 fun x ↦ LocalPrincipalPart.boundedBy_mono (h x) (mem_boundedBy_iff.1 hμ x)

theorem mapOfLE_mem_boundedBy (hD : D ≤ D') (hE : E ≤ E') {μ : PrincipalParts D}
    (hμ : μ ∈ boundedBy D E) : mapOfLE hD μ ∈ boundedBy D' E' :=
  mem_boundedBy_iff.2 fun x ↦ by
    rw [mapOfLE_apply]
    exact LocalPrincipalPart.mapOfLE_mem_boundedBy hD (hE x) (mem_boundedBy_iff.1 hμ x)

/-- For `D ≤ E`, the distributions bounded by `E` are those which vanish relative to `E`. -/
theorem boundedBy_eq_ker_mapOfLE (h : D ≤ E) : boundedBy D E = LinearMap.ker (mapOfLE h) := by
  ext μ
  simp only [mem_boundedBy_iff, LocalPrincipalPart.boundedBy_eq_ker_mapOfLE h, LinearMap.mem_ker,
    DFinsupp.ext_iff, mapOfLE_apply, DFinsupp.zero_apply]

/-- Where `E` permits no more poles than `D`, the only distribution bounded by `E` is zero. -/
theorem boundedBy_eq_bot (h : E ≤ D) : boundedBy D E = ⊥ := by
  rw [eq_bot_iff]
  intro μ hμ
  refine (Submodule.mem_bot ℂ).2 (DFinsupp.ext fun x ↦ ?_)
  simpa [LocalPrincipalPart.boundedBy_eq_bot (h x)] using mem_boundedBy_iff.1 hμ x

variable (D E) in
/-- The pointwise reading of a Mittag-Leffler distribution bounded by `E`. -/
private def toBoundedFamilyAux : boundedBy D E →ₗ[ℂ] ∀ x, LocalPrincipalPart.boundedBy D E x :=
  LinearMap.pi fun x ↦ (DFinsupp.lapply x).restrict fun _ hμ ↦ mem_boundedBy_iff.1 hμ x

/-- Every family of principal parts bounded by `E` is a Mittag-Leffler distribution: it vanishes
off the finite support of `E - D`. -/
private theorem toBoundedFamilyAux_bijective : Function.Bijective (toBoundedFamilyAux D E) := by
  classical
  refine ⟨fun μ ν h ↦ Subtype.ext (DFinsupp.ext fun x ↦ congrArg Subtype.val (congrFun h x)),
    fun c ↦ ?_⟩
  have hfin : {x | (c x : LocalPrincipalPart D x) ≠ 0}.Finite := by
    refine (E - D).support.finite_toSet.subset fun x hx ↦ ?_
    by_contra hmem
    have hED : E x ≤ D x := by
      simp [sub_eq_zero] at hmem
      exact hmem.le
    exact hx (by
      simpa using (Submodule.eq_bot_iff _).1 (LocalPrincipalPart.boundedBy_eq_bot hED) _
          (c x).property)
  refine ⟨⟨DFinsupp.ofSupportFinite (fun x ↦ (c x : LocalPrincipalPart D x)) hfin,
    mem_boundedBy_iff.2 fun x ↦ by simp [DFinsupp.ofSupportFinite_apply]⟩, ?_⟩
  funext x
  exact Subtype.ext (DFinsupp.ofSupportFinite_apply _ _ x)

variable (D E) in
/-- A Mittag-Leffler distribution bounded by `E` is the same as a family of local principal parts
bounded by `E`: such a family vanishes off the finite support of `E - D`. -/
def toBoundedFamily : boundedBy D E ≃ₗ[ℂ] ∀ x, LocalPrincipalPart.boundedBy D E x :=
  LinearEquiv.ofBijective (toBoundedFamilyAux D E) toBoundedFamilyAux_bijective

@[simp]
theorem coe_toBoundedFamily_apply (μ : boundedBy D E) (x : X) :
    (toBoundedFamily D E μ x : LocalPrincipalPart D x) = (μ : PrincipalParts D) x := (rfl)

@[simp]
theorem coe_toBoundedFamily_symm_apply (c : ∀ x, LocalPrincipalPart.boundedBy D E x) (x : X) :
    ((toBoundedFamily D E).symm c : PrincipalParts D) x = c x := by
  rw [← coe_toBoundedFamily_apply, LinearEquiv.apply_symm_apply]

/-- The **least bounding divisor** of a Mittag-Leffler distribution relative to `D`: its
coefficient at `x` is the pole bound of the local principal part at `x`. -/
def boundingDivisor (μ : PrincipalParts D) : WeilDivisor X :=
  D + Finsupp.ofSupportFinite (fun x ↦ LocalPrincipalPart.poleBound D (μ x) - D x) (by
    classical
    refine (μ.support.finite_toSet).subset fun x hx ↦ ?_
    by_contra hmem
    simp only [Finset.mem_coe, DFinsupp.mem_support_toFun, not_not] at hmem
    simp [hmem] at hx)

@[simp]
theorem boundingDivisor_apply (μ : PrincipalParts D) (x : X) :
    boundingDivisor μ x = LocalPrincipalPart.poleBound D (μ x) := by
  rw [boundingDivisor, Finsupp.add_apply, Finsupp.ofSupportFinite_coe]
  omega

theorem le_boundingDivisor (μ : PrincipalParts D) : D ≤ boundingDivisor μ := fun x ↦ by
  simpa using LocalPrincipalPart.le_poleBound (μ x)

theorem mem_boundedBy_boundingDivisor (μ : PrincipalParts D) :
    μ ∈ boundedBy D (boundingDivisor μ) :=
  mem_boundedBy_iff.2 fun x ↦ LocalPrincipalPart.mem_boundedBy_of_poleBound_le (by simp)

/-- The bounding divisor is least among the divisors `E ≥ D` bounding the distribution. -/
theorem boundingDivisor_le {μ : PrincipalParts D} (hD : D ≤ E) (hμ : μ ∈ boundedBy D E) :
    boundingDivisor μ ≤ E := fun x ↦ by
  simpa using LocalPrincipalPart.poleBound_le (hD x) (mem_boundedBy_iff.1 hμ x)

/-- A distribution is bounded by `E ≥ D` exactly when its least bounding divisor is at most `E`. -/
theorem mem_boundedBy_iff_boundingDivisor_le {μ : PrincipalParts D} (hD : D ≤ E) :
    μ ∈ boundedBy D E ↔ boundingDivisor μ ≤ E :=
  ⟨boundingDivisor_le hD, fun h ↦ boundedBy_mono h (mem_boundedBy_boundingDivisor μ)⟩

@[simp]
theorem boundingDivisor_zero : boundingDivisor (0 : PrincipalParts D) = D :=
  Finsupp.ext fun x ↦ by
    rw [boundingDivisor_apply, DFinsupp.zero_apply, LocalPrincipalPart.poleBound_zero]

/-- For `D ≤ D'` and `E ≤ E'`, the map from families of principal parts relative to `D` bounded by
`E` to families relative to `D'` bounded by `E'`, pointwise by `LocalPrincipalPart.mapOfLE`. -/
def boundedFamilyMap (hD : D ≤ D') (hE : E ≤ E') :
    (∀ x : X, LocalPrincipalPart.boundedBy D E x) →ₗ[ℂ]
      ∀ x : X, LocalPrincipalPart.boundedBy D' E' x :=
  LinearMap.piMap fun x ↦ LocalPrincipalPart.boundedByMapOfLE hD (hE x)

@[simp]
theorem coe_boundedFamilyMap_apply (hD : D ≤ D') (hE : E ≤ E')
    (c : ∀ x : X, LocalPrincipalPart.boundedBy D E x) (x : X) :
    (boundedFamilyMap hD hE c x : LocalPrincipalPart D' x) =
      LocalPrincipalPart.mapOfLE hD x (c x) := (rfl)

theorem boundedFamilyMap_toBoundedFamily (hD : D ≤ D') (hE : E ≤ E') (μ : boundedBy D E) :
    boundedFamilyMap hD hE (toBoundedFamily D E μ) =
      toBoundedFamily D' E' ⟨mapOfLE hD μ, mapOfLE_mem_boundedBy hD hE μ.property⟩ :=
  funext fun x ↦ Subtype.ext (by
    rw [coe_boundedFamilyMap_apply, coe_toBoundedFamily_apply, coe_toBoundedFamily_apply,
      mapOfLE_apply])

end Bounds

end PrincipalParts

namespace MeromorphicFunction

variable [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X]

/-- The principal part of `f` relative to `D` vanishes at `x` exactly when `f` satisfies the
order bound of `𝒪_D` at `x`. -/
theorem mk_toChartGerm_eq_zero_iff {D : WeilDivisor X} {x : X} {f : MeromorphicFunction X} :
    (Submodule.Quotient.mk (toChartGerm x f) : LocalPrincipalPart D x) = 0 ↔
      ((-D x : ℤ) : WithTop ℤ) ≤ order x f := by
  rw [Submodule.Quotient.mk_eq_zero, meromorphicGerms.mem_orderGE, order_toChartGerm]

/-- Away from the poles of `f` and the support of `D`, the order bound of `𝒪_D` holds. -/
private theorem neg_le_order_of_ne_infty_of_eq_zero {D : WeilDivisor X} {x : X}
    {f : MeromorphicFunction X} (hf : f x ≠ ∞) (hD : D x = 0) :
    ((-D x : ℤ) : WithTop ℤ) ≤ order x f := by
  rw [hD, neg_zero, WithTop.coe_zero]
  exact order_nonneg_iff.2 hf

variable [CompactSpace X]

/-- On a compact surface, the points where a meromorphic function violates the order bound
of `𝒪_D` form a finite set: they are poles of `f` or points of the support of `D`. -/
theorem finite_setOf_not_neg_le_order (D : WeilDivisor X) (f : MeromorphicFunction X) :
    {x | ¬((-D x : ℤ) : WithTop ℤ) ≤ order x f}.Finite := by
  refine (f.finite_setOf_eq_infty.union D.support.finite_toSet).subset fun x hx ↦ ?_
  by_contra hmem
  simp only [mem_union, mem_ofPred_eq, Finset.mem_coe, Finsupp.mem_support_iff, not_or,
    not_not] at hmem
  exact hx (neg_le_order_of_ne_infty_of_eq_zero hmem.1 hmem.2)

/-- The **principal parts** of a meromorphic function on a compact connected Riemann surface,
relative to a divisor `D`: at each point, the coordinate germ modulo the stalk of `𝒪_D`. Only
the poles of `f` and the points of the support of `D` contribute. -/
def principalParts (D : WeilDivisor X) : MeromorphicFunction X →ₗ[ℂ] PrincipalParts D where
  toFun f := DFinsupp.ofSupportFinite (fun x ↦ Submodule.Quotient.mk (toChartGerm x f))
    ((finite_setOf_not_neg_le_order D f).subset fun _ hx h ↦ hx (mk_toChartGerm_eq_zero_iff.2 h))
  map_add' f g := by
    ext x
    simp only [map_add, Submodule.Quotient.mk_add, DFinsupp.ofSupportFinite_apply,
      DFinsupp.coe_add, Pi.add_apply]
  map_smul' c f := by
    ext x
    simp only [map_smul, Submodule.Quotient.mk_smul, DFinsupp.ofSupportFinite_apply,
      DFinsupp.coe_smul, Pi.smul_apply, RingHom.id_apply]

@[simp]
theorem principalParts_apply (D : WeilDivisor X) (f : MeromorphicFunction X) (x : X) :
    principalParts D f x = Submodule.Quotient.mk (toChartGerm x f) :=
  DFinsupp.ofSupportFinite_apply _ _ x

/-- The principal part of `f` relative to `D` vanishes at `x` exactly when `f` satisfies the
order bound of `𝒪_D` at `x`. -/
theorem principalParts_apply_eq_zero_iff {D : WeilDivisor X} {f : MeromorphicFunction X}
    {x : X} : principalParts D f x = 0 ↔ ((-D x : ℤ) : WithTop ℤ) ≤ order x f := by
  rw [principalParts_apply, mk_toChartGerm_eq_zero_iff]

/-- Principal parts vanish away from the poles and the support of the divisor. -/
theorem principalParts_apply_eq_zero {D : WeilDivisor X} {f : MeromorphicFunction X} {x : X}
    (hf : f x ≠ ∞) (hD : D x = 0) : principalParts D f x = 0 :=
  principalParts_apply_eq_zero_iff.2 (neg_le_order_of_ne_infty_of_eq_zero hf hD)

/-- Taking principal parts commutes with the projection to a larger divisor. -/
@[simp]
theorem mapOfLE_principalParts {D E : WeilDivisor X} (h : D ≤ E) (f : MeromorphicFunction X) :
    PrincipalParts.mapOfLE h (principalParts D f) = principalParts E f :=
  DFinsupp.ext fun x ↦ by
    rw [PrincipalParts.mapOfLE_apply, principalParts_apply, principalParts_apply,
      LocalPrincipalPart.mapOfLE_mk]

/-- **Left exactness of the Mittag-Leffler sequence.** The meromorphic functions with zero
principal parts relative to `D` are exactly the global sections of `𝒪_D`:
`0 → H⁰(X, 𝒪_D) → 𝓜(X) → PrincipalParts D` is exact. -/
theorem ker_principalParts (D : WeilDivisor X) :
    LinearMap.ker (principalParts D) = LinearMap.range (divisorSections.toMeromorphic D) := by
  ext f
  rw [LinearMap.mem_ker, divisorSections.mem_range_toMeromorphic_iff, DFinsupp.ext_iff]
  exact forall_congr' fun x ↦ principalParts_apply_eq_zero_iff

end MeromorphicFunction

/-! ### Multiplication by meromorphic functions -/

section MeromorphicMul

variable [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X] {D E F : WeilDivisor X}

namespace LocalPrincipalPart

/-- If `ord_x f ≥ D x - E x`, multiplication by the coordinate germ of `f` sends germs of order at
least `-D x` to germs of order at least `-E x`. -/
theorem toChartGerm_mul_mem_orderGE {f : MeromorphicFunction X} {x : X}
    (hf : ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x f)
    {φ : meromorphicGerms ℂ (chartAt ℂ x x)}
    (hφ : φ ∈ meromorphicGerms.orderGE (chartAt ℂ x x) (-D x)) :
    MeromorphicFunction.toChartGerm x f * φ ∈ meromorphicGerms.orderGE (chartAt ℂ x x) (-E x) := by
  rw [meromorphicGerms.mem_orderGE] at hφ ⊢
  rw [meromorphicGerms.order_mul, MeromorphicFunction.order_toChartGerm]
  calc ((-E x : ℤ) : WithTop ℤ) = ((D x - E x : ℤ) : WithTop ℤ) + ((-D x : ℤ) : WithTop ℤ) := by
        norm_cast
        ring
    _ ≤ _ := add_le_add hf hφ

/-- **Multiplication of local principal parts by a meromorphic function** `f` with
`ord_x f ≥ D x - E x`: the class of a germ `φ` relative to `D` goes to the class of `f φ` relative
to `E`. -/
def meromorphicMul (f : MeromorphicFunction X) (x : X)
    (hf : ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x f) :
    LocalPrincipalPart D x →ₗ[ℂ] LocalPrincipalPart E x :=
  Submodule.mapQ _ _ (LinearMap.mulLeft ℂ (MeromorphicFunction.toChartGerm x f))
    fun _ hφ ↦ toChartGerm_mul_mem_orderGE hf hφ

@[simp]
theorem meromorphicMul_mk (f : MeromorphicFunction X) (x : X)
    (hf : ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x f)
    (φ : meromorphicGerms ℂ (chartAt ℂ x x)) :
    meromorphicMul f x hf (Submodule.Quotient.mk φ) =
      Submodule.Quotient.mk (MeromorphicFunction.toChartGerm x f * φ) :=
  (rfl)

end LocalPrincipalPart

namespace PrincipalParts

/-- **Multiplication of Mittag-Leffler distributions by a meromorphic function** `f` with
`ord f ≥ D - E`, pointwise by `TauCeti.RiemannSurface.LocalPrincipalPart.meromorphicMul`. -/
def meromorphicMul (f : MeromorphicFunction X)
    (hf : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x f) :
    PrincipalParts D →ₗ[ℂ] PrincipalParts E :=
  DFinsupp.mapRange.linearMap fun x ↦ LocalPrincipalPart.meromorphicMul f x (hf x)

@[simp]
theorem meromorphicMul_apply (f : MeromorphicFunction X)
    (hf : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x f)
    (μ : PrincipalParts D) (x : X) :
    meromorphicMul f hf μ x = LocalPrincipalPart.meromorphicMul f x (hf x) (μ x) :=
  (rfl)

/-- Multiplication of Mittag-Leffler distributions is additive in the meromorphic function. -/
theorem meromorphicMul_add {f g h : MeromorphicFunction X}
    (hf : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x f)
    (hg : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g)
    (hh : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x h) (hfg : h = f + g) :
    meromorphicMul h hh = meromorphicMul f hf + meromorphicMul g hg := by
  subst hfg
  ext μ x : 2
  simp only [LinearMap.add_apply, DFinsupp.coe_add, Pi.add_apply, meromorphicMul_apply]
  induction μ x using Submodule.Quotient.induction_on with
  | _ φ => simp only [LocalPrincipalPart.meromorphicMul_mk, map_add, add_mul,
    Submodule.Quotient.mk_add]

/-- Multiplication of Mittag-Leffler distributions is homogeneous in the meromorphic function. -/
theorem meromorphicMul_smul {f g : MeromorphicFunction X} (c : ℂ)
    (hf : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x f)
    (hg : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g) (hfg : g = c • f) :
    meromorphicMul g hg = c • meromorphicMul f hf := by
  subst hfg
  ext μ x : 2
  simp only [LinearMap.smul_apply, DFinsupp.coe_smul, Pi.smul_apply, meromorphicMul_apply]
  induction μ x using Submodule.Quotient.induction_on with
  | _ φ => simp only [LocalPrincipalPart.meromorphicMul_mk, map_smul, smul_mul_assoc,
    Submodule.Quotient.mk_smul]

/-- Multiplying by `g` and then by `f` with `f g = 1` is the projection to the larger divisor. -/
theorem meromorphicMul_meromorphicMul_eq_mapOfLE {f g : MeromorphicFunction X}
    (hf : ∀ x, ((E x - F x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x f)
    (hg : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g) (hfg : f * g = 1)
    (h : D ≤ F) (μ : PrincipalParts D) :
    meromorphicMul f hf (meromorphicMul g hg μ) = mapOfLE h μ := by
  ext x
  simp only [meromorphicMul_apply, mapOfLE_apply]
  induction μ x using Submodule.Quotient.induction_on with
  | _ φ => rw [LocalPrincipalPart.meromorphicMul_mk, LocalPrincipalPart.meromorphicMul_mk,
    LocalPrincipalPart.mapOfLE_mk, ← mul_assoc, ← map_mul, hfg, map_one, one_mul]

/-- Multiplication by `f` sends the principal parts of `g` to the principal parts of `f g`. -/
theorem meromorphicMul_principalParts [CompactSpace X] (f : MeromorphicFunction X)
    (hf : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x f)
    (g : MeromorphicFunction X) :
    meromorphicMul f hf (MeromorphicFunction.principalParts D g) =
      MeromorphicFunction.principalParts E (f * g) :=
  DFinsupp.ext fun x ↦ by
    rw [meromorphicMul_apply, MeromorphicFunction.principalParts_apply,
      MeromorphicFunction.principalParts_apply, LocalPrincipalPart.meromorphicMul_mk, map_mul]

end PrincipalParts

end MeromorphicMul

end TauCeti.RiemannSurface
