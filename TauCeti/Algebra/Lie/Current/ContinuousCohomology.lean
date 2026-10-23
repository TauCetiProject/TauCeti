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
* `TauCeti.CurrentAlgebra.residueClassEquiv`: the linear equivalence `t ↦ t • [c_Ψ]` from the
  scalars onto continuous second cohomology.
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
  obtain ⟨c, rfl⟩ := continuousSecondCohomologyMk_surjective a
  obtain ⟨t, f, hf, hc⟩ := exists_eq_smul_twoCochainOfBilinear_add_d₁₂ hΨ hΨs hspan hne c.2
  refine ⟨t, ?_⟩
  rw [residueClass_eq_mk, ← map_smul, continuousSecondCohomologyMk_eq_iff]
  exact ⟨f, hf, by
    simp only [SetLike.mk_smul_mk, AddSubgroupClass.coe_sub, hc]
    abel⟩

/-- **The continuous second cohomology of formal currents is one-dimensional.** Under the
hypotheses of `exists_eq_smul_twoCochainOfBilinear_add_d₁₂`, the map `t ↦ t • [c_Ψ]` is a linear
equivalence from the scalars onto the continuous second cohomology of formal currents with trivial
coefficients. -/
noncomputable def residueClassEquiv {Ψ : LinearMap.BilinForm K L} (hΨ : Ψ.lieInvariant L)
    (hΨs : Ψ.IsSymm)
    (hspan : ∀ Φ : LinearMap.BilinForm K L, Φ.lieInvariant L → ∃ t : K, Φ = t • Ψ)
    (hne : ∃ x y z : L, Ψ ⁅x, y⁆ z ≠ 0) :
    K ≃ₗ[K] continuousSecondCohomology K (currentAlgebra K L)
      (TrivialLieModule K (currentAlgebra K L) K) :=
  have hΨ0 : Ψ ≠ 0 := by
    rintro rfl
    obtain ⟨x, y, z, h⟩ := hne
    exact h rfl
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton K _ (residueClass K L Ψ hΨ hΨs))
    ⟨(injective_iff_map_eq_zero _).mpr fun t ↦ (smul_residueClass_eq_zero_iff hΨ hΨs hΨ0 t).mp,
      fun a ↦ (exists_eq_smul_residueClass hΨ hΨs hspan hne a).imp fun _ h ↦ h.symm⟩

@[simp]
theorem residueClassEquiv_apply {Ψ : LinearMap.BilinForm K L} (hΨ : Ψ.lieInvariant L)
    (hΨs : Ψ.IsSymm)
    (hspan : ∀ Φ : LinearMap.BilinForm K L, Φ.lieInvariant L → ∃ t : K, Φ = t • Ψ)
    (hne : ∃ x y z : L, Ψ ⁅x, y⁆ z ≠ 0) (t : K) :
    residueClassEquiv hΨ hΨs hspan hne t = t • residueClass K L Ψ hΨ hΨs :=
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
  (residueClassEquiv (_root_.LieModule.traceForm_lieInvariant K L L)
    (LinearMap.BilinForm.isSymm_iff.mpr (_root_.LieModule.traceForm_isSymm K L L))
    (fun _ hΦ ↦ TauCeti.LieAlgebra.exists_eq_smul_killingForm hΦ)
    exists_killingForm_lie_ne_zero).finrank_eq.symm.trans (Module.finrank_self K)

end Classification

end TauCeti.CurrentAlgebra
