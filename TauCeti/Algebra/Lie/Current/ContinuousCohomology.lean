/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Cohomology.Continuous
public import TauCeti.Algebra.Lie.Current.ResidueCocycle
public import TauCeti.Algebra.Lie.Current.Topology
public import TauCeti.Algebra.Lie.Loop.Cocycle
-- Non-public: used only inside proofs.
import TauCeti.Algebra.Lie.Killing.Basic
import TauCeti.Algebra.Lie.Killing.Perfect

/-!
# Continuous cochains on formal currents

For formal currents `R⸨X⸩ ⊗[R] L` with their order topology, the continuity conditions of
`TauCeti.LieModule.Cohomology` take the concrete form of the joint-continuity criterion: writing
`a_N` for the currents of order at least `N`, a one-cochain is continuous when it vanishes on some
`a_N`, and an alternating two-cochain `c` is continuous when each `c u` vanishes on some `a_N` and
`c` vanishes on `a_N × a_N` for a single `N`. Since the bracket of currents is continuous,
coboundaries of continuous one-cochains with trivial coefficients are continuous two-cocycles.

The residue cocycle `(f ⊗ x, g ⊗ y) ↦ Res(f dg) Φ(x, y)` of an invariant symmetric form `Φ` is
continuous: every current pairs to zero with all currents of sufficiently high order, and the
pairing vanishes on the positive currents `a_0`. Its class in continuous second cohomology is
therefore defined, and over a characteristic-zero domain it is nonzero, and has no torsion, as soon
as `Φ` is nonzero. Indeed no multiple `t • c_Φ` with `t ≠ 0` is a coboundary of any one-cochain,
continuous or not, since its restriction to polynomial currents is not.

Conversely, when `L` is finite-dimensional with nondegenerate Killing form over a field of
characteristic zero and `Ψ` spans the invariant forms, every continuous 2-cocycle `c` is
`t • c_Ψ + d₁₂ f` with `f` continuous. On polynomial currents, the classification of
`TauCeti.Algebra.Lie.Loop.Cocycle` writes `c` as `t • c_Ψ + d₁₂ g` for some one-cochain `g`. Joint
continuity makes `c` vanish on pairs of currents of order at least some `N₀ ≥ 1`; since `L` is
perfect, every mode `x_n` with `n ≥ 2 N₀` is a sum of brackets `⁅y_{N₀}, z_{n - N₀}⁆`, so `g`
vanishes on these modes. Composing `g` with truncation at `2 N₀` therefore gives a continuous
one-cochain `f` on formal currents extending `g`, and the continuous cochains `c` and
`t • c_Ψ + d₁₂ f` agree on the dense polynomial currents, hence everywhere. Density alone would not
suffice: it is the vanishing of `g` on high modes that makes `g` extend continuously. For a simple
Lie algebra over an algebraically closed field of characteristic zero, the continuous second
cohomology of its formal loop algebra is thus one-dimensional, spanned by the residue class of the
Killing form.

The classification extends to an arbitrary vector space `Z` of coefficients with trivial action, of
any dimension: `z ↦ [c_Ψ ⊗ z]`, the class of `(f ⊗ x, g ⊗ y) ↦ Res(f dg) Ψ(x, y) • z`, is a linear
equivalence from `Z` onto the continuous second cohomology with coefficients in `Z`. Injectivity
follows from the scalar case, since linear functionals separate the points of `Z`. For surjectivity,
each functional `φ` turns a continuous cocycle `c` into a scalar one, which is `t_φ • c_Ψ` up to a
coboundary. The scalars `t_φ` are the values `φ z` at a single vector `z`, read off from the values
of `c` at `(x_{-1}, y_1)` and `(x_0, y_0)`. Since formal currents are perfect, the difference
`c - c_Ψ ⊗ z` is then the coboundary of a one-cochain with values in `Z`, which vanishes on the
currents of order at least `2 N` when `c` vanishes on pairs of currents of order at least `N`. No
finite-dimensionality of `Z` is needed, as no basis of `Z` is used.

## Main results

* `TauCeti.CurrentAlgebra.mem_continuousTwoCochain_iff_orderSubmodule`: the joint-continuity
  criterion for two-cochains on formal currents.
* `TauCeti.CurrentAlgebra.d₁₂_mem_continuousTwoCocycle_of_isTrivial`: coboundaries of continuous
  one-cochains with trivial coefficients are continuous two-cocycles.
* `TauCeti.CurrentAlgebra.twoCochainOfBilinear_mem_continuousTwoCocycle`: the residue cocycle is
  continuous.
* `TauCeti.CurrentAlgebra.residueClass`: its class in continuous second cohomology.
* `TauCeti.CurrentAlgebra.smul_residueClass_eq_zero_iff`: a multiple of the residue class of a
  nonzero form vanishes only when the scalar does.
* `TauCeti.CurrentAlgebra.exists_eq_smul_twoCochainOfBilinear_add_d₁₂`: every continuous
  2-cocycle is a multiple of the residue cocycle plus a continuous coboundary.
* `TauCeti.CurrentAlgebra.exists_eq_smul_residueClass`: the residue class spans continuous second
  cohomology.
* `TauCeti.CurrentAlgebra.residueClassMap`: the residue class `z ↦ [c_Φ ⊗ z]` with coefficients
  in a module `Z` with trivial action.
* `TauCeti.CurrentAlgebra.residueClassMap_injective`: it is injective for a nonzero form over a
  characteristic-zero domain and projective `Z`.
* `TauCeti.CurrentAlgebra.exists_eq_twoCochainOfBilinearSMulRight_add_d₁₂`: every continuous
  2-cocycle with values in a vector space `Z` is a residue cocycle `c_Ψ ⊗ z` plus a continuous
  coboundary.
* `TauCeti.CurrentAlgebra.residueClassEquiv`: the linear equivalence `z ↦ [c_Ψ ⊗ z]` from any
  vector space `Z` onto continuous second cohomology with coefficients in `Z`.
* `TauCeti.CurrentAlgebra.finrank_continuousSecondCohomology_eq_one`: for a simple Lie algebra
  over an algebraically closed field of characteristic zero, continuous second cohomology of
  formal currents is one-dimensional.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.3, for the continuous cohomology of
  the formal loop algebra and its residue class.
-/

public section

noncomputable section

open Filter Topology
open scoped TensorProduct LaurentSeries

namespace TauCeti.CurrentAlgebra

open _root_.LieModule.Cohomology TauCeti.LieModule.Cohomology

-- The coefficientwise algebra structure matches the module used by the tensor product.
attribute [local instance 1100] HahnSeries.instAlgebra

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

/-- A one-cochain on formal currents is continuous exactly when it vanishes on all currents of
some order `N`. -/
theorem mem_continuousOneCochain_iff_orderSubmodule {f : oneCochain R (currentAlgebra R L) M} :
    f ∈ continuousOneCochain R (currentAlgebra R L) M ↔
      ∃ N : ℤ, ∀ u ∈ orderSubmodule R L N, f u = 0 := by
  simp [mem_continuousOneCochain_iff,
    (hasBasis_nhds_zero R L).eventually_iff]

/-- **The joint-continuity criterion on formal currents.** An alternating two-cochain `c` on
formal currents is continuous exactly when each partial map `c u` vanishes on the currents of some
order, and `c` vanishes on all pairs of currents of order at least a single `N`. -/
theorem mem_continuousTwoCochain_iff_orderSubmodule {c : twoCochain R (currentAlgebra R L) M} :
    c ∈ continuousTwoCochain R (currentAlgebra R L) M ↔
      (∀ u, ∃ N : ℤ, ∀ v ∈ orderSubmodule R L N, c u v = 0) ∧
        ∃ N : ℤ, ∀ u ∈ orderSubmodule R L N, ∀ v ∈ orderSubmodule R L N, c u v = 0 := by
  simp [mem_continuousTwoCochain_iff_of_hasBasis (hasBasis_nhds_zero R L)]

/-- Coboundaries of continuous one-cochains on formal currents with trivial coefficients are
continuous two-cocycles. -/
theorem d₁₂_mem_continuousTwoCocycle_of_isTrivial [LieRingModule (currentAlgebra R L) M]
    [LieModule R (currentAlgebra R L) M] [LieModule.IsTrivial (currentAlgebra R L) M]
    {f : oneCochain R (currentAlgebra R L) M}
    (hf : f ∈ continuousOneCochain R (currentAlgebra R L) M) :
    d₁₂ R (currentAlgebra R L) M f ∈ continuousTwoCocycle R (currentAlgebra R L) M :=
  d₁₂_mem_continuousTwoCocycle (continuous_lie R L)
    (fun m ↦ Eventually.of_forall fun u ↦ trivial_lie_zero _ M u m) hf

variable (R L)

/-- The residue 2-cochain of a symmetric form is continuous. -/
theorem twoCochainOfBilinear_mem_continuousTwoCochain (Φ : LinearMap.BilinForm R L)
    (hΦ : Φ.IsSymm) :
    twoCochainOfBilinear R L Φ hΦ ∈
      continuousTwoCochain R (currentAlgebra R L) (TrivialLieModule R (currentAlgebra R L) R) := by
  refine mem_continuousTwoCochain_iff_orderSubmodule.mpr ⟨fun u ↦ ?_, ⟨0, fun u hu v hv ↦ ?_⟩⟩
  · obtain ⟨N, hN⟩ := exists_orderSubmodule_le_ker_residuePairing R L Φ u
    exact ⟨N, fun v hv ↦ by simp [LinearMap.mem_ker.mp (hN hv)]⟩
  · simp [residuePairing_eq_zero_of_mem_orderSubmodule_zero R L Φ hu hv]

/-- The residue 2-cocycle of an invariant symmetric form is a continuous 2-cocycle. -/
theorem twoCochainOfBilinear_mem_continuousTwoCocycle (Φ : LinearMap.BilinForm R L)
    (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) :
    twoCochainOfBilinear R L Φ hΦs ∈
      continuousTwoCocycle R (currentAlgebra R L) (TrivialLieModule R (currentAlgebra R L) R) :=
  mem_continuousTwoCocycle_iff.mpr ⟨twoCochainOfBilinear_mem_continuousTwoCochain R L Φ hΦs,
    twoCocycleOfBilinear_coe R L Φ hΦ hΦs ▸ (twoCocycleOfBilinear R L Φ hΦ hΦs).2⟩

/-- The residue class of an invariant symmetric form `Φ`: the class of the residue cocycle
`(f ⊗ x, g ⊗ y) ↦ Res(f dg) Φ(x, y)` in the continuous second cohomology of formal currents with
trivial coefficients. -/
def residueClass (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) :
    continuousSecondCohomology R (currentAlgebra R L) (TrivialLieModule R (currentAlgebra R L) R) :=
  continuousSecondCohomologyMk _ _ _
    ⟨twoCochainOfBilinear R L Φ hΦs, twoCochainOfBilinear_mem_continuousTwoCocycle R L Φ hΦ hΦs⟩

variable {R L}

/-- The residue class is represented by the residue cocycle. -/
theorem residueClass_eq_mk (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L)
    (hΦs : Φ.IsSymm) :
    residueClass R L Φ hΦ hΦs = continuousSecondCohomologyMk _ _ _
      ⟨twoCochainOfBilinear R L Φ hΦs,
        twoCochainOfBilinear_mem_continuousTwoCocycle R L Φ hΦ hΦs⟩ :=
  (rfl)

/-- **The residue class of a nonzero form is torsion-free.** Over a characteristic-zero domain, a
multiple `t • [c_Φ]` of the residue class of a nonzero invariant symmetric form vanishes in
continuous second cohomology only for `t = 0`. -/
theorem smul_residueClass_eq_zero_iff [IsDomain R] [CharZero R] {Φ : LinearMap.BilinForm R L}
    (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (hΦ0 : Φ ≠ 0) (t : R) :
    t • residueClass R L Φ hΦ hΦs = 0 ↔ t = 0 := by
  refine ⟨fun h ↦ ?_, fun ht ↦ by simp [ht]⟩
  rw [residueClass_eq_mk, ← map_smul, continuousSecondCohomologyMk_eq_zero_iff] at h
  obtain ⟨f, -, hf⟩ := h
  let eC := TrivialLieModule.equiv R (currentAlgebra R L) R
  let eP := TrivialLieModule.equiv R (_root_.LieAlgebra.loopAlgebra R ℤ L) R
  -- Restricting the coboundary along the polynomial currents exhibits `t • c_Φ` as a coboundary
  -- on the loop algebra, which is impossible for `t ≠ 0`.
  refine (TauCeti.LieAlgebra.LoopAlgebra.smul_twoCochainOfBilinear_mem_range_d₁₂_iff hΦs hΦ0 t).mp
    ⟨(eP.symm.toLinearMap ∘ₗ eC.toLinearMap) ∘ₗ f ∘ₗ (ofLoop R L).toLinearMap, ?_⟩
  refine Subtype.ext (LinearMap.ext₂ fun u v ↦ eP.injective ?_)
  -- The differential of the restricted cochain is the restriction of `t • c_Φ`.
  have hd : eP (d₁₂ R _ _ ((eP.symm.toLinearMap ∘ₗ eC.toLinearMap) ∘ₗ f ∘ₗ
      (ofLoop R L).toLinearMap) u v) =
      t • eC (twoCochainOfBilinear R L Φ hΦs (ofLoop R L u) (ofLoop R L v)) := by
    rw [d₁₂_comp_lieHom_apply_apply_ofTrivial, hf]
    simp only [Submodule.coe_smul, smul_apply_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, map_smul]
  -- On polynomial currents, `c_Φ` is the residue cocycle of the loop algebra.
  have hres : eC (twoCochainOfBilinear R L Φ hΦs (ofLoop R L u) (ofLoop R L v)) =
      eP (_root_.LieAlgebra.LoopAlgebra.twoCochainOfBilinear R ℤ L Φ hΦs u v) :=
    twoCochainOfBilinear_ofLoop R L Φ hΦs u v
  simpa only [twoCochain_val_apply, Submodule.coe_smul, LinearMap.smul_apply, map_smul, hres]
    using hd

/-- The residue class of a nonzero invariant symmetric form over a characteristic-zero domain is
nonzero. -/
theorem residueClass_ne_zero [IsDomain R] [CharZero R] {Φ : LinearMap.BilinForm R L}
    (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (hΦ0 : Φ ≠ 0) :
    residueClass R L Φ hΦ hΦs ≠ 0 := by
  simpa using (smul_residueClass_eq_zero_iff hΦ hΦs hΦ0 1).not.mpr one_ne_zero

section Coefficients

variable {Z : Type*} [AddCommGroup Z] [Module R Z]

variable (R L) in
/-- The residue cochain with coefficients in a module `Z` with trivial action is a continuous
2-cocycle. -/
theorem twoCochainOfBilinearSMulRight_mem_continuousTwoCocycle (Φ : LinearMap.BilinForm R L)
    (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (z : Z) :
    twoCochainOfBilinearSMulRight R L Φ hΦs z ∈
      continuousTwoCocycle R (currentAlgebra R L) (TrivialLieModule R (currentAlgebra R L) Z) := by
  -- Push the scalar residue cocycle forward along `t ↦ t • z`.
  have h := twoCochainMap_id_mem_continuousTwoCocycle
    ((TrivialLieModule.equiv R (currentAlgebra R L) Z).symm.toLinearMap ∘ₗ
      LinearMap.toSpanSingleton R Z z ∘ₗ
      (TrivialLieModule.equiv R (currentAlgebra R L) R).toLinearMap)
    (twoCochainOfBilinear_mem_continuousTwoCocycle R L Φ hΦ hΦs)
  rwa [← twoCochainOfBilinearSMulRight_one, twoCochainMap_twoCochainOfBilinearSMulRight,
    LinearMap.toSpanSingleton_apply, one_smul] at h

variable (R L) in
/-- The residue class with coefficients in a module `Z` with trivial action: the linear map sending
`z : Z` to the class of the residue cocycle `(f ⊗ x, g ⊗ y) ↦ Res(f dg) Φ(x, y) • z` in the
continuous second cohomology of formal currents. For `Z = R` it sends `t` to `t • residueClass`.
-/
def residueClassMap (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) :
    Z →ₗ[R] continuousSecondCohomology R (currentAlgebra R L)
      (TrivialLieModule R (currentAlgebra R L) Z) :=
  continuousSecondCohomologyMk _ _ _ ∘ₗ (twoCochainOfBilinearSMulRight R L Φ hΦs).codRestrict _
    (twoCochainOfBilinearSMulRight_mem_continuousTwoCocycle R L Φ hΦ hΦs)

/-- The residue class with coefficients in `Z` is represented by the residue cocycle. -/
theorem residueClassMap_apply (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L)
    (hΦs : Φ.IsSymm) (z : Z) :
    residueClassMap R L Φ hΦ hΦs z = continuousSecondCohomologyMk _ _ _
      ⟨twoCochainOfBilinearSMulRight R L Φ hΦs z,
        twoCochainOfBilinearSMulRight_mem_continuousTwoCocycle R L Φ hΦ hΦs z⟩ :=
  (rfl)

/-- For `Z = R`, the residue class with coefficient `t` is `t • residueClass`. -/
@[simp]
theorem residueClassMap_self (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L)
    (hΦs : Φ.IsSymm) (t : R) :
    residueClassMap R L Φ hΦ hΦs t = t • residueClass R L Φ hΦ hΦs := by
  conv_lhs => rw [← mul_one t, ← smul_eq_mul, map_smul]
  simp only [residueClassMap_apply, residueClass_eq_mk, twoCochainOfBilinearSMulRight_one]

/-- **Residue classes with coefficients detect their coefficient.** Over a characteristic-zero
domain, the residue class of a nonzero invariant symmetric form with coefficients in a projective
module `Z`, for instance any vector space, is injective in its coefficient. -/
theorem residueClassMap_injective [IsDomain R] [CharZero R] [Module.Projective R Z]
    {Φ : LinearMap.BilinForm R L} (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (hΦ0 : Φ ≠ 0) :
    Function.Injective (residueClassMap R L Φ hΦ hΦs (Z := Z)) := by
  refine (injective_iff_map_eq_zero _).mpr fun z hz ↦ ?_
  rw [residueClassMap_apply, continuousSecondCohomologyMk_eq_zero_iff] at hz
  obtain ⟨f, hf, hdf⟩ := hz
  refine (Module.forall_dual_apply_eq_zero_iff R z).mp fun φ ↦ ?_
  -- Pushing the coboundary forward along `φ` shows that `φ z • [c_Φ] = 0`.
  let e : TrivialLieModule R (currentAlgebra R L) Z →ₗ[R]
      TrivialLieModule R (currentAlgebra R L) R :=
    (TrivialLieModule.equiv R _ R).symm.toLinearMap ∘ₗ φ ∘ₗ
      (TrivialLieModule.equiv R _ Z).toLinearMap
  refine (smul_residueClass_eq_zero_iff hΦ hΦs hΦ0 (φ z)).mp ?_
  rw [← residueClassMap_self, residueClassMap_apply, continuousSecondCohomologyMk_eq_zero_iff]
  refine ⟨e ∘ₗ f, comp_mem_continuousOneCochain e hf, ?_⟩
  have h := congrArg (twoCochainMap e LieHom.id) hdf
  rw [twoCochainMap_twoCochainOfBilinearSMulRight] at h
  refine Eq.trans (Subtype.ext (LinearMap.ext₂ fun u v ↦ ?_)) (h.trans (by simp))
  simp [trivial_lie_zero]

end Coefficients

section Classification

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [_root_.LieAlgebra.IsKilling K L]

open _root_.LieAlgebra

/-- **Every continuous 2-cocycle on formal currents is a residue cocycle up to a continuous
coboundary.** Let `L` be a finite-dimensional Lie algebra with nondegenerate Killing form over a
field of characteristic zero, and `Ψ` an invariant symmetric form on `L` spanning the invariant
forms and nonzero on some bracket. Every continuous 2-cocycle with trivial coefficients on formal
currents is `t • c_Ψ + d₁₂ f` for a scalar `t` and a continuous one-cochain `f`. -/
theorem exists_eq_smul_twoCochainOfBilinear_add_d₁₂ {Ψ : LinearMap.BilinForm K L}
    (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm)
    (hspan : ∀ Φ : LinearMap.BilinForm K L, Φ.lieInvariant L → ∃ t : K, Φ = t • Ψ)
    (hne : ∃ x y z : L, Ψ ⁅x, y⁆ z ≠ 0) {c : twoCochain K (currentAlgebra K L)
      (TrivialLieModule K (currentAlgebra K L) K)}
    (hc : c ∈ continuousTwoCocycle K (currentAlgebra K L)
      (TrivialLieModule K (currentAlgebra K L) K)) :
    ∃ t : K, ∃ f ∈ continuousOneCochain K (currentAlgebra K L)
        (TrivialLieModule K (currentAlgebra K L) K),
      c = t • twoCochainOfBilinear K L Ψ hΨs + d₁₂ K _ _ f := by
  set eC := TrivialLieModule.equiv K (currentAlgebra K L) K
  set eP := TrivialLieModule.equiv K (loopAlgebra K ℤ L) K
  obtain ⟨hcc, hcz⟩ := mem_continuousTwoCocycle_iff.mp hc
  -- On polynomial currents, `c` is `t • c_Ψ + d₁₂ g` for some, a priori discontinuous, `g`.
  have hcP := twoCochainMap_mem_twoCocycle (eP.symm.toLinearMap ∘ₗ eC.toLinearMap) (ofLoop K L)
    hcz
  rw [TauCeti.LieAlgebra.LoopAlgebra.twoCocycle_eq_span_sup_range_d₁₂ hΨ hΨs hspan hne,
    Submodule.mem_sup] at hcP
  obtain ⟨_, hts, _, ⟨g, rfl⟩, hcP⟩ := hcP
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hts
  have hcP_apply (u v : loopAlgebra K ℤ L) : eC (c (ofLoop K L u) (ofLoop K L v)) =
      t * eP (LoopAlgebra.twoCochainOfBilinear K ℤ L Ψ hΨs u v) - eP (g ⁅u, v⁆) := by
    have h := congrArg (fun c' ↦ eP (c' u v)) hcP
    simp only [twoCochainMap_apply_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, add_apply_apply, smul_apply_apply, map_add, map_smul,
      d₁₂_apply_apply_ofTrivial, map_neg, smul_eq_mul] at h
    rw [← h, sub_eq_add_neg]
  -- By joint continuity, `c` vanishes on pairs of currents of order at least `N₀ ≥ 1`.
  obtain ⟨N, hN⟩ := (mem_continuousTwoCochain_iff_orderSubmodule.mp hcc).2
  set N₀ := max N 1
  have hmode (a : ℤ) (x : L) (ha : N₀ ≤ a) :
      ofLoop K L (AddMonoidAlgebra.single a 1 ⊗ₜ x) ∈ orderSubmodule K L N :=
    orderSubmodule_antitone K L (le_trans (le_max_left N 1) ha)
      (ofLoop_single_tmul_mem_orderSubmodule K L a x)
  -- Hence `g` vanishes on the modes `x_n` with `n ≥ 2 N₀`: since `L` is perfect, `x_n` is a sum
  -- of brackets of modes of order at least `N₀`, on which both `c` and `c_Ψ` vanish.
  have hg_mode (n : ℤ) (hn : 2 * N₀ ≤ n) (x : L) : g (AddMonoidAlgebra.single n 1 ⊗ₜ x) = 0 := by
    have hx := TauCeti.LieAlgebra.LoopAlgebra.single_add_tmul_mem_span_lie
      (derivedSeries_one_eq_top_of_isKilling K L) N₀ (n - N₀) x
    rw [add_sub_cancel] at hx
    refine LinearMap.mem_ker.mp (Submodule.span_le.mpr ?_ hx)
    rintro _ ⟨y, z, rfl⟩
    have h := hcP_apply (AddMonoidAlgebra.single N₀ 1 ⊗ₜ y)
      (AddMonoidAlgebra.single (n - N₀) 1 ⊗ₜ z)
    rw [hN _ (hmode _ _ le_rfl) _ (hmode _ _ (by omega))] at h
    simp only [map_zero, LoopAlgebra.twoCochainOfBilinear_apply_apply,
      TauCeti.LieAlgebra.LoopAlgebra.residuePairing_single_tmul,
      show N₀ + (n - N₀) ≠ 0 by omega, ↓reduceIte, mul_zero, zero_sub, zero_eq_neg] at h
    exact eP.injective (by rw [h, map_zero])
  -- Truncating at `2 N₀` extends `g` to a continuous one-cochain `f` on formal currents.
  set f : oneCochain K (currentAlgebra K L) (TrivialLieModule K (currentAlgebra K L) K) :=
    eC.symm.toLinearMap ∘ₗ eP.toLinearMap ∘ₗ g ∘ₗ trunc K L (2 * N₀)
  have hf : f ∈ continuousOneCochain K (currentAlgebra K L)
      (TrivialLieModule K (currentAlgebra K L) K) :=
    mem_continuousOneCochain_iff_orderSubmodule.mpr ⟨2 * N₀, fun u hu ↦ by
      simp [f, trunc_eq_zero_of_mem_orderSubmodule K L hu]⟩
  have hf_ofLoop (p : loopAlgebra K ℤ L) : eC (f (ofLoop K L p)) = eP (g p) := by
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      apply_trunc_ofLoop K L g hg_mode]
  -- Both sides are continuous and agree on the dense polynomial currents.
  refine ⟨t, f, hf, continuousTwoCochain_ext_on hcc
    (add_mem (Submodule.smul_mem _ t (twoCochainOfBilinear_mem_continuousTwoCochain K L Ψ hΨs))
      (mem_continuousTwoCocycle_iff.mp (d₁₂_mem_continuousTwoCocycle_of_isTrivial hf)).1)
    (denseRange_ofLoop K L) ?_⟩
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
  apply eC.injective
  simp only [hcP_apply, add_apply_apply, smul_apply_apply, map_add, map_smul,
    d₁₂_apply_apply_ofTrivial, map_neg, ← LieHom.map_lie, hf_ofLoop, smul_eq_mul]
  rw [twoCochainOfBilinear_ofLoop]
  ring

variable {Z : Type*} [AddCommGroup Z] [Module K Z]

/-- **Every continuous 2-cocycle with discrete coefficients is a residue cocycle up to a continuous
coboundary.** Under the hypotheses of `exists_eq_smul_twoCochainOfBilinear_add_d₁₂`, let `Z` be any
vector space with trivial action, of arbitrary dimension. Every continuous 2-cocycle on formal
currents with values in `Z` is `c_Ψ ⊗ z + d₁₂ f` for a vector `z` and a continuous one-cochain `f`.
-/
theorem exists_eq_twoCochainOfBilinearSMulRight_add_d₁₂ {Ψ : LinearMap.BilinForm K L}
    (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm)
    (hspan : ∀ Φ : LinearMap.BilinForm K L, Φ.lieInvariant L → ∃ t : K, Φ = t • Ψ)
    (hne : ∃ x y z : L, Ψ ⁅x, y⁆ z ≠ 0) {c : twoCochain K (currentAlgebra K L)
      (TrivialLieModule K (currentAlgebra K L) Z)}
    (hc : c ∈ continuousTwoCocycle K (currentAlgebra K L)
      (TrivialLieModule K (currentAlgebra K L) Z)) :
    ∃ z : Z, ∃ f ∈ continuousOneCochain K (currentAlgebra K L)
        (TrivialLieModule K (currentAlgebra K L) Z),
      c = twoCochainOfBilinearSMulRight K L Ψ hΨs z + d₁₂ K _ _ f := by
  set eK := TrivialLieModule.equiv K (currentAlgebra K L) K
  -- Each functional `φ` on the coefficients turns `c` into a scalar continuous cocycle, which by
  -- the scalar classification is `t φ • c_Ψ + d₁₂ (f φ)` with `f φ` continuous.
  choose t f _ hcf using fun φ : Module.Dual K (TrivialLieModule K (currentAlgebra K L) Z) ↦
    exists_eq_smul_twoCochainOfBilinear_add_d₁₂ hΨ hΨs hspan hne
      (twoCochainMap_id_mem_continuousTwoCocycle (eK.symm.toLinearMap ∘ₗ φ) hc)
  have hcf_apply (φ) (a b : currentAlgebra K L) :
      φ (c a b) = t φ * residuePairing K L Ψ a b - eK (f φ ⁅a, b⁆) := by
    simpa [eK, sub_eq_add_neg, trivial_lie_zero] using congrArg (fun c' ↦ eK (c' a b)) (hcf φ)
  -- The scalar `t φ` is `φ z` for an explicit vector `z`, read off from the values of `c` on
  -- `(x_{-1}, y_1)` and `(x_0, y_0)`: these pairs have the same bracket, so coboundaries take the
  -- same value on both, while the residue cochain differs by `Ψ(x, y) ≠ 0`.
  obtain ⟨x, y, hxy⟩ : ∃ x y : L, Ψ x y ≠ 0 := by
    obtain ⟨x₁, x₂, y, h⟩ := hne
    exact ⟨_, y, h⟩
  set a₁ : currentAlgebra K L := HahnSeries.single (-1) 1 ⊗ₜ x
  set b₁ : currentAlgebra K L := HahnSeries.single 1 1 ⊗ₜ y
  set a₀ : currentAlgebra K L := HahnSeries.single 0 1 ⊗ₜ x
  set b₀ : currentAlgebra K L := HahnSeries.single 0 1 ⊗ₜ y
  have hab : ⁅a₁, b₁⁆ = ⁅a₀, b₀⁆ := by
    simp [a₁, b₁, a₀, b₀, ExtendScalars.bracket_tmul, HahnSeries.single_mul_single]
  have hres : residuePairing K L Ψ a₁ b₁ - residuePairing K L Ψ a₀ b₀ = Ψ x y := by
    simp [a₁, b₁, a₀, b₀, residuePairing_tmul, LaurentSeries.residuePairing_single]
  set z := (Ψ x y)⁻¹ • (c a₁ b₁ - c a₀ b₀)
  have ht (φ) : t φ = φ z := by
    have h₁ := hcf_apply φ a₁ b₁
    rw [hab] at h₁
    rw [map_smul, map_sub, h₁, hcf_apply, smul_eq_mul]
    field_simp
    linear_combination -t φ * hres
  -- Hence, for `c' = c - c_Ψ ⊗ z`, every `φ ∘ c'` is a coboundary, and so is `c'` itself because
  -- formal currents are perfect.
  have hperf := derivedSeries_one_eq_top_of_isKilling K L
  set c' := c - twoCochainOfBilinearSMulRight K L Ψ hΨs (TrivialLieModule.equiv K _ Z z)
  obtain ⟨F, hF⟩ := exists_d₁₂_eq_of_forall_dual (derivedSeries_one_eq_top K L hperf) c' fun φ ↦
    ⟨eK.toLinearMap ∘ₗ f φ, fun a b ↦ by simp [c', hcf_apply, ht, eK, mul_comm]⟩
  -- By joint continuity `c'` vanishes on pairs of currents of order at least some `N ≥ 0`, so `F`
  -- vanishes on currents of order at least `2 N`, which are sums of brackets of such pairs.
  obtain ⟨N₁, hN₁⟩ := (mem_continuousTwoCochain_iff_orderSubmodule.mp
    (mem_continuousTwoCocycle_iff.mp hc).1).2
  set N := max N₁ 0
  have hN (a : currentAlgebra K L) (ha : a ∈ orderSubmodule K L N) (b : currentAlgebra K L)
      (hb : b ∈ orderSubmodule K L N) : F ⁅a, b⁆ = 0 := by
    have h₁ := orderSubmodule_antitone K L (le_max_left N₁ 0)
    have h₀ := orderSubmodule_antitone K L (le_max_right N₁ 0)
    have h := congrArg (fun c'' ↦ c'' a b) hF
    simpa [c', trivial_lie_zero, hN₁ a (h₁ ha) b (h₁ hb),
      residuePairing_eq_zero_of_mem_orderSubmodule_zero K L Ψ (h₀ ha) (h₀ hb)] using h
  refine ⟨TrivialLieModule.equiv K _ Z z, F, mem_continuousOneCochain_iff_orderSubmodule.mpr
    ⟨N + N, orderSubmodule_add_le_ker_of_map_lie_eq_zero K L hperf F hN⟩, ?_⟩
  rw [hF]
  exact (add_sub_cancel _ c).symm

/-- **Continuous second cohomology with discrete coefficients is spanned by residue classes.**
Under the hypotheses of `exists_eq_smul_twoCochainOfBilinear_add_d₁₂`, the residue class map with
coefficients in any vector space `Z` with trivial action is surjective. -/
theorem residueClassMap_surjective {Ψ : LinearMap.BilinForm K L} (hΨ : Ψ.lieInvariant L)
    (hΨs : Ψ.IsSymm)
    (hspan : ∀ Φ : LinearMap.BilinForm K L, Φ.lieInvariant L → ∃ t : K, Φ = t • Ψ)
    (hne : ∃ x y z : L, Ψ ⁅x, y⁆ z ≠ 0) :
    Function.Surjective (residueClassMap K L Ψ hΨ hΨs (Z := Z)) := by
  intro a
  obtain ⟨c, rfl⟩ := continuousSecondCohomologyMk_surjective a
  obtain ⟨z, f, hf, hc⟩ := exists_eq_twoCochainOfBilinearSMulRight_add_d₁₂ hΨ hΨs hspan hne c.2
  refine ⟨z, ?_⟩
  rw [residueClassMap_apply, continuousSecondCohomologyMk_eq_iff]
  exact ⟨-f, neg_mem hf, by
    simp only [map_neg, AddSubgroupClass.coe_sub, hc]
    abel⟩

/-- **The continuous second cohomology of formal currents is spanned by the residue class.**
Under the hypotheses of `exists_eq_smul_twoCochainOfBilinear_add_d₁₂`, every class in the
continuous second cohomology of formal currents with trivial coefficients is a multiple of the
residue class of `Ψ`. -/
theorem exists_eq_smul_residueClass {Ψ : LinearMap.BilinForm K L} (hΨ : Ψ.lieInvariant L)
    (hΨs : Ψ.IsSymm)
    (hspan : ∀ Φ : LinearMap.BilinForm K L, Φ.lieInvariant L → ∃ t : K, Φ = t • Ψ)
    (hne : ∃ x y z : L, Ψ ⁅x, y⁆ z ≠ 0)
    (a : continuousSecondCohomology K (currentAlgebra K L)
      (TrivialLieModule K (currentAlgebra K L) K)) :
    ∃ t : K, a = t • residueClass K L Ψ hΨ hΨs := by
  obtain ⟨t, rfl⟩ := residueClassMap_surjective (Z := K) hΨ hΨs hspan hne a
  exact ⟨t, residueClassMap_self Ψ hΨ hΨs t⟩

variable (Z) in
/-- **Continuous second cohomology of formal currents with discrete coefficients.** Under the
hypotheses of `exists_eq_smul_twoCochainOfBilinear_add_d₁₂`, for every vector space `Z` with
trivial action, of arbitrary dimension, the residue class map `z ↦ [c_Ψ ⊗ z]` is a linear
equivalence from `Z` onto the continuous second cohomology of formal currents with coefficients in
`Z`. For `Z = K` it sends `t` to `t • residueClass` (`residueClassMap_self`). -/
noncomputable def residueClassEquiv {Ψ : LinearMap.BilinForm K L} (hΨ : Ψ.lieInvariant L)
    (hΨs : Ψ.IsSymm)
    (hspan : ∀ Φ : LinearMap.BilinForm K L, Φ.lieInvariant L → ∃ t : K, Φ = t • Ψ)
    (hne : ∃ x y z : L, Ψ ⁅x, y⁆ z ≠ 0) :
    Z ≃ₗ[K] continuousSecondCohomology K (currentAlgebra K L)
      (TrivialLieModule K (currentAlgebra K L) Z) :=
  have hΨ0 : Ψ ≠ 0 := by
    rintro rfl
    obtain ⟨x, y, z, h⟩ := hne
    exact h rfl
  LinearEquiv.ofBijective (residueClassMap K L Ψ hΨ hΨs)
    ⟨residueClassMap_injective hΨ hΨs hΨ0, residueClassMap_surjective hΨ hΨs hspan hne⟩

@[simp]
theorem residueClassEquiv_apply {Ψ : LinearMap.BilinForm K L} (hΨ : Ψ.lieInvariant L)
    (hΨs : Ψ.IsSymm)
    (hspan : ∀ Φ : LinearMap.BilinForm K L, Φ.lieInvariant L → ∃ t : K, Φ = t • Ψ)
    (hne : ∃ x y z : L, Ψ ⁅x, y⁆ z ≠ 0) (z : Z) :
    residueClassEquiv Z hΨ hΨs hspan hne z = residueClassMap K L Ψ hΨ hΨs z :=
  (rfl)

variable (K L) in
/-- **The continuous second cohomology of the formal loop algebra of a simple Lie algebra is
one-dimensional.** Here `L` is a finite-dimensional Lie algebra over an algebraically closed field
of characteristic zero whose adjoint module is irreducible and whose Killing form is
nondegenerate, for instance a simple Lie algebra; the residue class of the Killing form spans. -/
theorem finrank_continuousSecondCohomology_eq_one [IsAlgClosed K]
    [_root_.LieModule.IsIrreducible K L L] :
    Module.finrank K (continuousSecondCohomology K (currentAlgebra K L)
      (TrivialLieModule K (currentAlgebra K L) K)) = 1 :=
  have _i := _root_.LieModule.nontrivial_of_isIrreducible K L L
  (residueClassEquiv K (_root_.LieModule.traceForm_lieInvariant K L L)
    (LinearMap.BilinForm.isSymm_iff.mpr (_root_.LieModule.traceForm_isSymm K L L))
    (fun _ hΦ ↦ TauCeti.LieAlgebra.exists_eq_smul_killingForm hΦ)
    exists_killingForm_lie_ne_zero).finrank_eq.symm.trans (Module.finrank_self K)

end Classification

end TauCeti.CurrentAlgebra
