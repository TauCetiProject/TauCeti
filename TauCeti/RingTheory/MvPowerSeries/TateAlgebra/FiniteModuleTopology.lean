/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Submodule
public import TauCeti.Topology.Algebra.Module.Finite
public import TauCeti.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.LocalAtTarget
import TauCeti.Analysis.Normed.Module.StrictGenerators

/-!
# Canonical topology, strict maps, and bounded lifts for finite modules over Tate algebras

Let `T = K⟨X₁/c₁, …, Xₙ/cₙ⟩` be a restricted power-series algebra in finitely many variables at
positive radii over a complete nonarchimedean field `K` (or, more generally, `R{X/c}` over a
complete commutative ring `R` with a multiplicative ultrametric norm and a compatible Euclidean
degree). Every submodule of a finite free `T`-module `T^m` has a finite strict generating system and
is strictly closed (`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Submodule`). Combining this with
the presentation API in `TauCeti.Topology.Algebra.Module.ModuleTopology`,
`TauCeti.Topology.Algebra.Module.Finite`, and `TauCeti.Analysis.Normed.Module.StrictGenerators`
yields the topological and quantitative theory of finite `T`-modules without assuming that `K` is
nontrivially normed, spherically complete, or discretely valued:

* **Hausdorff canonical topology:** for a finite `T`-module `M`, `moduleTopology T M` is Hausdorff
  (`TauCeti.MvPowerSeries.t2Space_moduleTopology_isRestricted_subring`), complementing first
  countability (`TauCeti.firstCountableTopology_moduleTopology`), nonarchimedeanness
  (`TauCeti.nonarchimedeanAddGroup_moduleTopology`), completeness of the right uniformity
  (`TauCeti.completeSpace_moduleTopology`), and independence of finite presentation
  (`LinearMap.presentationContinuousLinearEquiv`).
* **Closed submodules and subspace topology:** every submodule `S` of a finite `T`-module `M`
  carrying `IsModuleTopology T M` is closed
  (`Submodule.isClosed_of_isModuleTopology_isRestricted_subring`), and its subspace topology is
  again the `T`-module topology (`Submodule.isModuleTopology_of_isRestricted_subring`).
* **Closed range and strictness of linear maps:** every `T`-linear map `f : M →ₗ[T] N` into a finite
  `T`-module `N` with `IsModuleTopology T N` has closed range
  (`LinearMap.isClosed_range_of_isRestricted_subring`); if `M` also carries `IsModuleTopology T M`
  (without any finiteness assumption on `M`), `f` is automatically continuous and strict
  (`LinearMap.isStrictMap_of_isRestricted_subring`), so `ContinuousLinearEquiv.quotKerEquivRange`
  identifies `M ⧸ ker f` topologically with `range f` in its subspace topology.
* **Uniformly norm-bounded preimages:** every `T`-linear map from a seminormed `T`-module into
  `T`, `T ⧸ I`, `ι → T`, or `(ι → T) ⧸ N` has linear preimage bounds on its range
  (`LinearMap.exists_preimage_norm_le_isRestricted_subring`,
  `LinearMap.exists_preimage_norm_le_ideal_quotient_isRestricted_subring`,
  `LinearMap.exists_preimage_norm_le_pi_isRestricted_subring`,
  `LinearMap.exists_preimage_norm_le_quotient_isRestricted_subring`).

When `K` is nontrivially normed, `TauCeti.Huber.IsTateRing.of_normedAlgebra` and
`TauCeti.Huber.IsTateRing.isModuleTopology` supply `IsModuleTopology T M` for any finitely
generated complete Hausdorff first-countable topological `T`-module `M`. Over a trivially normed
field (`K` discrete), requiring `IsModuleTopology T M` directly is sharp: a vector space over a
discrete field equipped with a nondiscrete norm does not carry the module topology.

## References

* S. Bosch, *Lectures on Formal and Rigid Geometry*, §1.3, Corollaries 8–10.
* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §§3.7.2–3.7.3, 5.2.7, and 6.1.1.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries Topology

section Euclidean

variable {σ R : Type*} [NormedCommRing R] [NormMulClass R] [IsUltrametricDist R]
  [CompleteSpace R] [Finite σ] {c : σ → ℝ} [∀ i, Fact (0 < c i)]

local notation "T" => IsRestricted.subring (R := R) c

/-- **The module topology on a finite module over restricted power series is Hausdorff.** Under the
Euclidean-normed-ring hypotheses of `exists_finset_eq_sum_smul_isRestricted_subring_of_division`,
the kernel of any finite free presentation `T^n → M` is closed, so `moduleTopology T M` is `T₂`. -/
theorem t2Space_moduleTopology_isRestricted_subring_of_division
    (deg : R → ℕ) (hdeg : ∀ x y : R, ‖x - y‖ < ‖x‖ → deg y = deg x)
    (hdiv : ∀ x y : R, x ≠ 0 → ∃ z w, y = z * x + w ∧ ‖w‖ ≤ ‖y‖ ∧ (w = 0 ∨ deg w < deg x))
    {M : Type*} [AddCommGroup M] [Module T M] [Module.Finite T M] :
    @T2Space M (moduleTopology T M) := by
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' T M
  exact (TauCeti.t2Space_moduleTopology_iff_isClosed_ker hq).mpr
    (isClosed_submodule_pi_isRestricted_subring_of_division deg hdeg hdiv (LinearMap.ker q))

/-- **Submodules of finite modules over restricted power series are closed.** Under the
Euclidean-normed-ring hypotheses, every submodule `S` of a finite `T`-module `M` carrying the module
topology is closed in `M`. -/
theorem isClosed_submodule_of_isModuleTopology_isRestricted_subring_of_division
    (deg : R → ℕ) (hdeg : ∀ x y : R, ‖x - y‖ < ‖x‖ → deg y = deg x)
    (hdiv : ∀ x y : R, x ≠ 0 → ∃ z w, y = z * x + w ∧ ‖w‖ ≤ ‖y‖ ∧ (w = 0 ∨ deg w < deg x))
    {M : Type*} [AddCommGroup M] [Module T M] [Module.Finite T M]
    [TopologicalSpace M] [IsModuleTopology T M] (S : Submodule T M) :
    IsClosed (S : Set M) := by
  have _ : T2Space (M ⧸ S) := by
    rw [_root_.eq_moduleTopology T (M ⧸ S)]
    exact t2Space_moduleTopology_isRestricted_subring_of_division deg hdeg hdiv
  have _ : ContinuousAdd (M ⧸ S) := IsModuleTopology.toContinuousAdd T (M ⧸ S)
  have hS : (S : Set M) = S.mkQ ⁻¹' {0} := by
    ext x
    simp [Submodule.Quotient.mk_eq_zero]
  rw [hS]
  exact isClosed_singleton.preimage (IsModuleTopology.continuous_of_linearMap S.mkQ)

/-- **Submodules of finite modules over restricted power series carry the module topology.** Under
the Euclidean-normed-ring hypotheses, for every submodule `S` of a finite `T`-module `M` carrying
the module topology, the subspace topology on `S` is `moduleTopology T S`. -/
theorem isModuleTopology_submodule_isRestricted_subring_of_division
    (deg : R → ℕ) (hdeg : ∀ x y : R, ‖x - y‖ < ‖x‖ → deg y = deg x)
    (hdiv : ∀ x y : R, x ≠ 0 → ∃ z w, y = z * x + w ∧ ‖w‖ ≤ ‖y‖ ∧ (w = 0 ∨ deg w < deg x))
    {M : Type*} [AddCommGroup M] [Module T M] [Module.Finite T M]
    [TopologicalSpace M] [IsModuleTopology T M] (S : Submodule T M) :
    IsModuleTopology T S := by
  have _ : IsTopologicalAddGroup M := IsModuleTopology.isTopologicalAddGroup T M
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' T M
  have hquot : IsOpenQuotientMap p := IsModuleTopology.isOpenQuotientMap_of_surjective hp
  have _ : IsModuleTopology T (S.comap p) :=
    (S.comap p).isModuleTopology_of_exists_finset_eq_sum_smul
      (exists_finset_eq_sum_smul_isRestricted_subring_of_division deg hdeg hdiv (S.comap p))
  let pS : S.comap p →ₗ[T] S := p.restrict fun _ hx ↦ hx
  have hpS_surj : Function.Surjective pS := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hp y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hpS_quot : IsQuotientMap pS :=
    (hquot.restrictPreimage (S : Set M)).isQuotientMap
  exact ⟨hpS_quot.eq_coinduced.trans (ModuleTopology.eq_coinduced_of_surjective hpS_surj).symm⟩

/-- **Linear maps into a finite module over restricted power series have closed range.** Neither
finiteness nor a topology on the source module `M` is required. -/
theorem isClosed_range_isRestricted_subring_of_division
    (deg : R → ℕ) (hdeg : ∀ x y : R, ‖x - y‖ < ‖x‖ → deg y = deg x)
    (hdiv : ∀ x y : R, x ≠ 0 → ∃ z w, y = z * x + w ∧ ‖w‖ ≤ ‖y‖ ∧ (w = 0 ∨ deg w < deg x))
    {M N : Type*} [AddCommGroup M] [Module T M]
    [AddCommGroup N] [Module T N] [Module.Finite T N] [TopologicalSpace N] [IsModuleTopology T N]
    (f : M →ₗ[T] N) :
    IsClosed (LinearMap.range f : Set N) :=
  isClosed_submodule_of_isModuleTopology_isRestricted_subring_of_division deg hdeg hdiv
    (LinearMap.range f)

/-- **Linear maps into a finite module over restricted power series are strict.** If `M` carries
the `T`-module topology and `N` is a finite `T`-module carrying the `T`-module topology, every
`T`-linear map `f : M →ₗ[T] N` is strict (continuous, and open onto its range with the subspace
topology). -/
theorem isStrictMap_isRestricted_subring_of_division
    (deg : R → ℕ) (hdeg : ∀ x y : R, ‖x - y‖ < ‖x‖ → deg y = deg x)
    (hdiv : ∀ x y : R, x ≠ 0 → ∃ z w, y = z * x + w ∧ ‖w‖ ≤ ‖y‖ ∧ (w = 0 ∨ deg w < deg x))
    {M N : Type*} [AddCommGroup M] [Module T M] [TopologicalSpace M] [IsModuleTopology T M]
    [AddCommGroup N] [Module T N] [Module.Finite T N] [TopologicalSpace N] [IsModuleTopology T N]
    (f : M →ₗ[T] N) :
    IsStrictMap f :=
  f.isStrictMap_of_isModuleTopology_range
    (isModuleTopology_submodule_isRestricted_subring_of_division deg hdeg hdiv (LinearMap.range f))

/-- **Bounded preimages for linear maps into finite free modules over restricted power series.** -/
theorem exists_preimage_norm_le_pi_isRestricted_subring_of_division
    (deg : R → ℕ) (hdeg : ∀ x y : R, ‖x - y‖ < ‖x‖ → deg y = deg x)
    (hdiv : ∀ x y : R, x ≠ 0 → ∃ z w, y = z * x + w ∧ ‖w‖ ≤ ‖y‖ ∧ (w = 0 ∨ deg w < deg x))
    {ι M : Type*} [Fintype ι] [SeminormedAddCommGroup M] [Module T M] [IsBoundedSMul T M]
    (f : M →ₗ[T] (ι → T)) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ LinearMap.range f, ∃ x : M, f x = y ∧ ‖x‖ ≤ C * ‖y‖ :=
  f.exists_preimage_norm_le_of_exists_finset_eq_sum_smul
    (exists_finset_eq_sum_smul_isRestricted_subring_of_division deg hdeg hdiv (LinearMap.range f))

/-- **Bounded preimages for linear maps into presented finite modules over restricted power
series.** Every `T`-linear map from a seminormed `T`-module into `(ι → T) ⧸ N` (with its quotient
maximum Gauss norm) admits a constant `C > 0` lifting every element of its range with norm
multiplied by at most `C`. -/
theorem exists_preimage_norm_le_quotient_isRestricted_subring_of_division
    (deg : R → ℕ) (hdeg : ∀ x y : R, ‖x - y‖ < ‖x‖ → deg y = deg x)
    (hdiv : ∀ x y : R, x ≠ 0 → ∃ z w, y = z * x + w ∧ ‖w‖ ≤ ‖y‖ ∧ (w = 0 ∨ deg w < deg x))
    {ι M : Type*} [Fintype ι] [SeminormedAddCommGroup M] [Module T M] [IsBoundedSMul T M]
    {N : Submodule T (ι → T)} (f : M →ₗ[T] ((ι → T) ⧸ N)) :
    ∃ C : ℝ, 0 < C ∧ ∀ q ∈ LinearMap.range f, ∃ x : M, f x = q ∧ ‖x‖ ≤ C * ‖q‖ :=
  f.exists_preimage_norm_le_quotient_of_exists_finset_eq_sum_smul
    (fun q _ ↦ Submodule.Quotient.exists_mk_eq_and_norm_eq_iff.mpr
      (exists_norm_sub_le_pi_isRestricted_subring_of_division deg hdeg hdiv N) q)
    (exists_finset_eq_sum_smul_isRestricted_subring_of_division deg hdeg hdiv
      ((LinearMap.range f).comap N.mkQ))

end Euclidean

section NoncommEuclidean

variable {σ R : Type*} [NormedRing R] [NormMulClass R] [IsUltrametricDist R]
  [CompleteSpace R] [Finite σ] {c : σ → ℝ} [∀ i, Fact (0 < c i)]

local notation "T" => IsRestricted.subring (R := R) c

/-- **Bounded preimages for linear maps into restricted power series.** Neither commutativity of
`R` nor finiteness of `M` is required. -/
theorem exists_preimage_norm_le_isRestricted_subring_of_division
    (deg : R → ℕ) (hdeg : ∀ x y : R, ‖x - y‖ < ‖x‖ → deg y = deg x)
    (hdiv : ∀ x y : R, x ≠ 0 → ∃ z w, y = z * x + w ∧ ‖w‖ ≤ ‖y‖ ∧ (w = 0 ∨ deg w < deg x))
    {M : Type*} [SeminormedAddCommGroup M] [Module T M] [IsBoundedSMul T M]
    (f : M →ₗ[T] T) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ LinearMap.range f, ∃ x : M, f x = y ∧ ‖x‖ ≤ C * ‖y‖ :=
  f.exists_preimage_norm_le_of_exists_finset_eq_sum_smul (by
    simpa only [smul_eq_mul] using
      exists_finset_eq_sum_mul_isRestricted_subring_of_division deg hdeg hdiv (LinearMap.range f))

/-- **Bounded preimages for linear maps into quotients of restricted power series by left
ideals.** -/
theorem exists_preimage_norm_le_ideal_quotient_isRestricted_subring_of_division
    (deg : R → ℕ) (hdeg : ∀ x y : R, ‖x - y‖ < ‖x‖ → deg y = deg x)
    (hdiv : ∀ x y : R, x ≠ 0 → ∃ z w, y = z * x + w ∧ ‖w‖ ≤ ‖y‖ ∧ (w = 0 ∨ deg w < deg x))
    {M : Type*} [SeminormedAddCommGroup M] [Module T M] [IsBoundedSMul T M]
    {I : Ideal T} (f : M →ₗ[T] (T ⧸ I)) :
    ∃ C : ℝ, 0 < C ∧ ∀ q ∈ LinearMap.range f, ∃ x : M, f x = q ∧ ‖x‖ ≤ C * ‖q‖ :=
  f.exists_preimage_norm_le_quotient_of_exists_finset_eq_sum_smul
    (fun q _ ↦ Submodule.Quotient.exists_mk_eq_and_norm_eq_iff.mpr
      (exists_norm_sub_le_isRestricted_subring_of_division deg hdeg hdiv I) q)
    (by
      simpa only [smul_eq_mul] using exists_finset_eq_sum_mul_isRestricted_subring_of_division
        deg hdeg hdiv ((LinearMap.range f).comap I.mkQ))

end NoncommEuclidean

section DivisionRing

variable {K σ : Type*} [NormedDivisionRing K] [IsUltrametricDist K] [CompleteSpace K] [Finite σ]
  {c : σ → ℝ} [∀ i, Fact (0 < c i)]

local notation "T" => IsRestricted.subring (R := K) c

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem exists_eq_mul_add_of_divisionRing (x y : K) (hx : x ≠ 0) :
    ∃ z w, y = z * x + w ∧ ‖w‖ ≤ ‖y‖ ∧ (w = 0 ∨ (0 : ℕ) < 0) :=
  ⟨y * x⁻¹, 0, by rw [add_zero, inv_mul_cancel_right₀ hx], by simp, Or.inl rfl⟩

/-- **Uniformly norm-bounded preimages for linear maps into a Tate algebra**
(S. Bosch, *Lectures on Formal and Rigid Geometry*, §1.3, Corollary 10). -/
theorem _root_.LinearMap.exists_preimage_norm_le_isRestricted_subring
    {M : Type*} [SeminormedAddCommGroup M] [Module T M] [IsBoundedSMul T M]
    (f : M →ₗ[T] T) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ LinearMap.range f, ∃ x : M, f x = y ∧ ‖x‖ ≤ C * ‖y‖ :=
  exists_preimage_norm_le_isRestricted_subring_of_division (fun _ ↦ 0) (fun _ _ _ ↦ rfl)
    exists_eq_mul_add_of_divisionRing f

/-- **Uniformly norm-bounded preimages for linear maps into a quotient of a Tate algebra by an
ideal** (S. Bosch, *Lectures on Formal and Rigid Geometry*, §1.3, Corollary 10). -/
theorem _root_.LinearMap.exists_preimage_norm_le_ideal_quotient_isRestricted_subring
    {M : Type*} [SeminormedAddCommGroup M] [Module T M] [IsBoundedSMul T M]
    {I : Ideal T} (f : M →ₗ[T] (T ⧸ I)) :
    ∃ C : ℝ, 0 < C ∧ ∀ q ∈ LinearMap.range f, ∃ x : M, f x = q ∧ ‖x‖ ≤ C * ‖q‖ :=
  exists_preimage_norm_le_ideal_quotient_isRestricted_subring_of_division (fun _ ↦ 0)
    (fun _ _ _ ↦ rfl) exists_eq_mul_add_of_divisionRing f

end DivisionRing

section Field

variable {K σ : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Finite σ]
  {c : σ → ℝ} [∀ i, Fact (0 < c i)]

local notation "T" => IsRestricted.subring (R := K) c

/-- **The module topology on a finite module over a Tate algebra is Hausdorff**
(S. Bosch, *Lectures on Formal and Rigid Geometry*, §1.3, Corollary 8). Over any complete
nonarchimedean field `K` (including trivially normed fields), for every finite module `M` over
`T = K⟨X/c⟩`, `moduleTopology T M` is `T₂`. -/
theorem t2Space_moduleTopology_isRestricted_subring
    {M : Type*} [AddCommGroup M] [Module T M] [Module.Finite T M] :
    @T2Space M (moduleTopology T M) :=
  t2Space_moduleTopology_isRestricted_subring_of_division (fun _ ↦ 0) (fun _ _ _ ↦ rfl)
    exists_eq_mul_add_of_divisionRing

/-- **Every submodule of a finite module over a Tate algebra is closed in the module topology**
(S. Bosch, *Lectures on Formal and Rigid Geometry*, §1.3, Corollary 9). -/
theorem _root_.Submodule.isClosed_of_isModuleTopology_isRestricted_subring
    {M : Type*} [AddCommGroup M] [Module T M] [Module.Finite T M]
    [TopologicalSpace M] [IsModuleTopology T M] (S : Submodule T M) :
    IsClosed (S : Set M) :=
  isClosed_submodule_of_isModuleTopology_isRestricted_subring_of_division (fun _ ↦ 0)
    (fun _ _ _ ↦ rfl) exists_eq_mul_add_of_divisionRing S

/-- **Every submodule of a finite module over a Tate algebra carries the module topology as its
subspace topology** (S. Bosch, *Lectures on Formal and Rigid Geometry*, §1.3, Corollary 9). -/
theorem _root_.Submodule.isModuleTopology_of_isRestricted_subring
    {M : Type*} [AddCommGroup M] [Module T M] [Module.Finite T M]
    [TopologicalSpace M] [IsModuleTopology T M] (S : Submodule T M) :
    IsModuleTopology T S :=
  isModuleTopology_submodule_isRestricted_subring_of_division (fun _ ↦ 0) (fun _ _ _ ↦ rfl)
    exists_eq_mul_add_of_divisionRing S

/-- **Every linear map into a finite module over a Tate algebra has closed range**
(S. Bosch, *Lectures on Formal and Rigid Geometry*, §1.3, Corollary 9). Neither finiteness nor a
topology on the source module `M` is required. -/
theorem _root_.LinearMap.isClosed_range_of_isRestricted_subring
    {M N : Type*} [AddCommGroup M] [Module T M]
    [AddCommGroup N] [Module T N] [Module.Finite T N] [TopologicalSpace N] [IsModuleTopology T N]
    (f : M →ₗ[T] N) :
    IsClosed (LinearMap.range f : Set N) :=
  isClosed_range_isRestricted_subring_of_division (fun _ ↦ 0) (fun _ _ _ ↦ rfl)
    exists_eq_mul_add_of_divisionRing f

/-- **Every linear map from a module with the module topology into a finite module over a Tate
algebra is strict** (S. Bosch, *Lectures on Formal and Rigid Geometry*, §1.3, Corollary 9): it is
continuous and open onto its range with the subspace topology, so
`ContinuousLinearEquiv.quotKerEquivRange` gives a topological isomorphism
`(M ⧸ ker f) ≃L[T] range f`. Finiteness is required only on the target `N`. -/
theorem _root_.LinearMap.isStrictMap_of_isRestricted_subring
    {M N : Type*} [AddCommGroup M] [Module T M] [TopologicalSpace M] [IsModuleTopology T M]
    [AddCommGroup N] [Module T N] [Module.Finite T N] [TopologicalSpace N] [IsModuleTopology T N]
    (f : M →ₗ[T] N) :
    IsStrictMap f :=
  isStrictMap_isRestricted_subring_of_division (fun _ ↦ 0) (fun _ _ _ ↦ rfl)
    exists_eq_mul_add_of_divisionRing f

/-- **Uniformly norm-bounded preimages for linear maps into finite free modules over Tate algebras**
(S. Bosch, *Lectures on Formal and Rigid Geometry*, §1.3, Corollary 10). -/
theorem _root_.LinearMap.exists_preimage_norm_le_pi_isRestricted_subring
    {ι M : Type*} [Fintype ι] [SeminormedAddCommGroup M] [Module T M] [IsBoundedSMul T M]
    (f : M →ₗ[T] (ι → T)) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ LinearMap.range f, ∃ x : M, f x = y ∧ ‖x‖ ≤ C * ‖y‖ :=
  exists_preimage_norm_le_pi_isRestricted_subring_of_division (fun _ ↦ 0) (fun _ _ _ ↦ rfl)
    exists_eq_mul_add_of_divisionRing f

/-- **Uniformly norm-bounded preimages for linear maps into presented finite modules over Tate
algebras** (S. Bosch, *Lectures on Formal and Rigid Geometry*, §1.3, Corollary 10). Every `T`-linear
map from a seminormed `T`-module `M` into `(ι → T) ⧸ N` (equipped with its quotient Gauss norm)
admits `C > 0` such that every `q ∈ LinearMap.range f` lifts to `x : M` with `‖x‖ ≤ C * ‖q‖`. -/
theorem _root_.LinearMap.exists_preimage_norm_le_quotient_isRestricted_subring
    {ι M : Type*} [Fintype ι] [SeminormedAddCommGroup M] [Module T M] [IsBoundedSMul T M]
    {N : Submodule T (ι → T)} (f : M →ₗ[T] ((ι → T) ⧸ N)) :
    ∃ C : ℝ, 0 < C ∧ ∀ q ∈ LinearMap.range f, ∃ x : M, f x = q ∧ ‖x‖ ≤ C * ‖q‖ :=
  exists_preimage_norm_le_quotient_isRestricted_subring_of_division (fun _ ↦ 0) (fun _ _ _ ↦ rfl)
    exists_eq_mul_add_of_divisionRing f

end Field

end TauCeti.MvPowerSeries
