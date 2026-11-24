/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import TauCeti.Algebra.Homology.ModuleCat.HomologyImage

/-!
# Spectral invariants of filtered homology

Let `M` be a module with an increasing family `I : ℝ → Submodule R M`, for instance the
filtration of a Floer homology group by the images `I a = im(FH^{<a} → FH)` of the homology of
the generators of action below `a`. The **spectral invariant** of `σ ∈ M` is the infimum

`ρ(σ) = inf {a | σ ∈ I a} ∈ [-∞, ∞]`

(`TauCeti.spectralInvariant`), the lowest action level at which `σ` is represented. It is `+∞`
when `σ` is represented at no level and `-∞` when it is represented at every level.

**Valuation properties.** Like the filtration levels of chains in Usher's framework of
Floer-type complexes, the spectral invariant behaves as a non-Archimedean valuation:
`ρ(0) = -∞`, `ρ(-σ) = ρ(σ)`, `ρ(r • σ) ≤ ρ(σ)`, and for an increasing filtration
`ρ(σ + τ) ≤ max ρ(σ) ρ(τ)`.

**Shifts of filtrations.** If a linear map `f : M → N` carries `I a` into `J (a + E)` for every
`a`, then `ρ_J(f σ) ≤ ρ_I(σ) + E` (`TauCeti.spectralInvariant_map_le`). This is the algebraic
content of the Hofer continuity of spectral invariants: the continuation map from the Floer
complex of a Hamiltonian `H⁺` to that of `H⁻` raises the action by at most
`E = ∫₀¹ max (H⁺_t - H⁻_t) dt`, and it commutes with the identifications of both Floer homologies
with a common symplectic homology group, so the spectral invariant of a class of that group with
respect to `H⁻` exceeds the one with respect to `H⁺` by at most `E`
(`TauCeti.spectralInvariant_symm_apply_le_of_comp_eq`). Exchanging the two Hamiltonians bounds
the difference by the Hofer norm of `H⁺ - H⁻`.

**Spectrality.** Suppose that the filtration is left continuous, every `I a` being the union of
the `I b` for `b < a`, and that it does not jump just after any level outside a set `S`. Then a
finite spectral invariant lies in `S` (`TauCeti.mem_of_spectralInvariant_eq_coe`).

**Filtered homology.** For a complex of modules `K` filtered in degree `n` by submodules
`F a ⊆ K.X n`, the induced filtration of the homology `H_n(K)` consists of the classes represented
by a cycle in `F a` (`HomologicalComplex.moduleCatHomologyImage`). For the action filtration
`F a = ⨆_{act x < a} V x` spanned by a family of generators `V x` with actions `act x`
(`TauCeti.actionFiltration`) this filtration is left continuous, and when the set of actions is
closed it jumps only at actions. So the spectral invariant of a class, when finite, is the action
of a generator (`TauCeti.mem_range_of_spectralInvariant_eq_coe`). For finitely many generators
spanning the term, the spectral invariant of every nonzero class is the action of a generator
(`TauCeti.exists_spectralInvariant_eq`): this is the spectrality of spectral invariants of a
nondegenerate Hamiltonian, whose Floer complex has finitely many generators, the `1`-periodic
orbits, with their actions. Chain maps raising the action by at most `E` raise spectral
invariants of homology classes by at most `E` (`TauCeti.spectralInvariant_homologyMap_le`,
`TauCeti.map_actionFiltration_le`).

## Main definitions

* `TauCeti.spectralInvariant I σ`: the spectral invariant of `σ` for the filtration `I`.
* `TauCeti.actionFiltration V act a`: the sum of the submodules `V x` over the generators `x` of
  action `act x < a`.

## Main results

* `TauCeti.spectralInvariant_lt_iff`, `TauCeti.spectralInvariant_le_iff`: the spectral invariant
  is below `a` exactly when `σ` is represented below `a`, and at most `a` exactly when `σ` is
  represented at every level above `a`.
* `TauCeti.spectralInvariant_add_le`: the triangle inequality `ρ(σ + τ) ≤ max ρ(σ) ρ(τ)`.
* `TauCeti.spectralInvariant_map_le`: maps shifting the filtration by `E` raise the spectral
  invariant by at most `E`.
* `TauCeti.mem_of_spectralInvariant_eq_coe`: spectrality for a left continuous filtration.
* `TauCeti.spectralInvariant_homologyMap_le`: chain maps shifting the filtration by `E` raise
  spectral invariants of homology classes by at most `E`.
* `TauCeti.exists_spectralInvariant_eq`: with finitely many generators, the spectral invariant of
  a nonzero homology class is the action of a generator.

## References

* M. Schwarz, *On the action spectrum for closed symplectically aspherical manifolds*, Pacific J.
  Math. 193 (2000), 419–461.
* M. Usher, *Spectral numbers in Floer theories*, Compos. Math. 144 (2008), 1581–1592.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §5.1, Proposition 5.8 and its proof.
-/

public section

open CategoryTheory HomologicalComplex

namespace TauCeti

section Module

variable {R : Type*} [Ring R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- The **spectral invariant** of `σ` for a family `I : ℝ → Submodule R M` of submodules, usually
increasing: the infimum in `[-∞, ∞]` of the levels `a` with `σ ∈ I a`. For the filtration of
Floer homology by the images of the homology of the subcomplexes of action below `a`, it is the
lowest action at which `σ` is represented. -/
noncomputable def spectralInvariant (I : ℝ → Submodule R M) (σ : M) : EReal :=
  ⨅ (a : ℝ) (_ : σ ∈ I a), (a : EReal)

variable {I : ℝ → Submodule R M} {J : ℝ → Submodule R N} {σ τ : M}

/-- A lower bound for the spectral invariant is a lower bound for every level at which `σ` is
represented. -/
theorem le_spectralInvariant_iff {x : EReal} :
    x ≤ spectralInvariant I σ ↔ ∀ a : ℝ, σ ∈ I a → x ≤ a :=
  le_iInf₂_iff

/-- The spectral invariant is at most every level at which `σ` is represented. -/
theorem spectralInvariant_le_of_mem {a : ℝ} (h : σ ∈ I a) : spectralInvariant I σ ≤ a :=
  iInf₂_le a h

/-- The spectral invariant is below `x` exactly when `σ` is represented at a level below `x`. -/
theorem spectralInvariant_lt_iff {x : EReal} :
    spectralInvariant I σ < x ↔ ∃ a : ℝ, σ ∈ I a ∧ (a : EReal) < x := by
  simp only [spectralInvariant, iInf_lt_iff, exists_prop]

/-- For an increasing filtration, `σ` is represented at every level above its spectral
invariant. -/
theorem mem_of_spectralInvariant_lt (hI : Monotone I) {a : ℝ} (h : spectralInvariant I σ < a) :
    σ ∈ I a := by
  obtain ⟨b, hb, hba⟩ := spectralInvariant_lt_iff.1 h
  exact hI (EReal.coe_lt_coe_iff.1 hba).le hb

/-- For an increasing filtration, the spectral invariant is at most `a` exactly when `σ` is
represented at every level above `a`. -/
theorem spectralInvariant_le_iff (hI : Monotone I) {a : ℝ} :
    spectralInvariant I σ ≤ a ↔ ∀ b : ℝ, a < b → σ ∈ I b := by
  refine ⟨fun h b hab ↦ mem_of_spectralInvariant_lt hI (h.trans_lt (EReal.coe_lt_coe_iff.2 hab)),
    fun h ↦ EReal.le_of_forall_lt_iff_le.1 fun b hab ↦ ?_⟩
  exact spectralInvariant_le_of_mem (h b (EReal.coe_lt_coe_iff.1 hab))

/-- The spectral invariant is `+∞` exactly when `σ` is represented at no level. -/
@[simp]
theorem spectralInvariant_eq_top_iff : spectralInvariant I σ = ⊤ ↔ ∀ a : ℝ, σ ∉ I a := by
  simp [spectralInvariant]

/-- If `σ` is represented at every level, its spectral invariant is `-∞`. -/
theorem spectralInvariant_eq_bot_of_forall_mem (h : ∀ a : ℝ, σ ∈ I a) :
    spectralInvariant I σ = ⊥ := by
  refine (EReal.eq_bot_iff_forall_lt _).2 fun a ↦ spectralInvariant_lt_iff.2 ⟨a - 1, h _, ?_⟩
  exact EReal.coe_lt_coe_iff.2 (sub_one_lt a)

/-- For an increasing filtration, the spectral invariant is `-∞` exactly when `σ` is represented
at every level. -/
theorem spectralInvariant_eq_bot_iff (hI : Monotone I) :
    spectralInvariant I σ = ⊥ ↔ ∀ a : ℝ, σ ∈ I a :=
  ⟨fun h a ↦ mem_of_spectralInvariant_lt hI (h ▸ EReal.bot_lt_coe a),
    spectralInvariant_eq_bot_of_forall_mem⟩

/-- The zero element is represented at every level, so its spectral invariant is `-∞`. -/
@[simp]
theorem spectralInvariant_zero : spectralInvariant I 0 = ⊥ :=
  spectralInvariant_eq_bot_of_forall_mem fun _ ↦ zero_mem _

/-- The spectral invariant does not see signs. -/
@[simp]
theorem spectralInvariant_neg : spectralInvariant I (-σ) = spectralInvariant I σ := by
  simp only [spectralInvariant, neg_mem_iff]

/-- A larger filtration gives smaller spectral invariants. -/
theorem spectralInvariant_anti {I' : ℝ → Submodule R M} (h : ∀ a, I a ≤ I' a) :
    spectralInvariant I' σ ≤ spectralInvariant I σ :=
  le_spectralInvariant_iff.2 fun _ ha ↦ spectralInvariant_le_of_mem (h _ ha)

/-- Multiplying by a scalar does not raise the spectral invariant. -/
theorem spectralInvariant_smul_le (r : R) : spectralInvariant I (r • σ) ≤ spectralInvariant I σ :=
  le_spectralInvariant_iff.2 fun _ ha ↦ spectralInvariant_le_of_mem (Submodule.smul_mem _ r ha)

/-- **The triangle inequality** for spectral invariants of an increasing filtration:
`ρ(σ + τ) ≤ max ρ(σ) ρ(τ)`. -/
theorem spectralInvariant_add_le (hI : Monotone I) :
    spectralInvariant I (σ + τ) ≤ max (spectralInvariant I σ) (spectralInvariant I τ) := by
  refine EReal.le_of_forall_lt_iff_le.1 fun a ha ↦ spectralInvariant_le_of_mem (add_mem ?_ ?_)
  · exact mem_of_spectralInvariant_lt hI ((le_max_left _ _).trans_lt ha)
  · exact mem_of_spectralInvariant_lt hI ((le_max_right _ _).trans_lt ha)

/-- **Maps shifting the filtration.** If `f` carries `I a` into `J (a + E)` for every level `a`,
then `ρ_J(f σ) ≤ ρ_I(σ) + E`. -/
theorem spectralInvariant_map_le (f : M →ₗ[R] N) {E : ℝ} (h : ∀ a, (I a).map f ≤ J (a + E))
    (σ : M) : spectralInvariant J (f σ) ≤ spectralInvariant I σ + E := by
  refine EReal.le_of_forall_lt_iff_le.1 fun z hz ↦ ?_
  have hlt : spectralInvariant I σ < ((z - E : ℝ) : EReal) := by
    rw [EReal.coe_sub]
    exact (EReal.lt_sub_iff_add_lt (.inl (EReal.coe_ne_bot E)) (.inl (EReal.coe_ne_top E))).2 hz
  obtain ⟨a, ha, haz⟩ := spectralInvariant_lt_iff.1 hlt
  refine (spectralInvariant_le_of_mem (h a ⟨σ, ha, rfl⟩)).trans (EReal.coe_le_coe_iff.2 ?_)
  linarith [EReal.coe_lt_coe_iff.1 haz]

/-- Transporting a filtration along a linear equivalence does not change spectral
invariants. -/
@[simp]
theorem spectralInvariant_map_linearEquiv (e : M ≃ₗ[R] N) (σ : M) :
    spectralInvariant (fun a ↦ (I a).map (e : M →ₗ[R] N)) (e σ) = spectralInvariant I σ := by
  simp only [spectralInvariant, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

/-- **The Hofer estimate.** Let `Ψ₁ : M ≃ S` and `Ψ₂ : N ≃ S` identify two filtered modules with a
common module `S`, and let `Φ : M → N` raise the filtration by at most `E` and commute with these
identifications. Then the spectral invariants of every `σ ∈ S` computed through `M` and through
`N` satisfy `ρ_J(Ψ₂⁻¹ σ) ≤ ρ_I(Ψ₁⁻¹ σ) + E`. For Floer homologies of two Hamiltonians identified
with a symplectic homology group, with `Φ` the continuation map, this is the Hofer continuity of
spectral invariants. -/
theorem spectralInvariant_symm_apply_le_of_comp_eq {S : Type*} [AddCommGroup S] [Module R S]
    (Φ : M →ₗ[R] N) (Ψ₁ : M ≃ₗ[R] S) (Ψ₂ : N ≃ₗ[R] S) (hΦ : (Ψ₂ : N →ₗ[R] S) ∘ₗ Φ = Ψ₁) {E : ℝ}
    (h : ∀ a, (I a).map Φ ≤ J (a + E)) (σ : S) :
    spectralInvariant J (Ψ₂.symm σ) ≤ spectralInvariant I (Ψ₁.symm σ) + E := by
  have : Ψ₂.symm σ = Φ (Ψ₁.symm σ) := by
    rw [LinearEquiv.symm_apply_eq]
    simpa using (LinearMap.congr_fun hΦ (Ψ₁.symm σ)).symm
  rw [this]
  exact spectralInvariant_map_le Φ h _

/-- **Spectrality.** Let `I` be an increasing filtration which is left continuous, every `I a`
being contained in the union of the `I b` for `b < a`, and which does not jump just after any
level outside a set `S`. Then a finite spectral invariant lies in `S`. -/
theorem mem_of_spectralInvariant_eq_coe (hI : Monotone I)
    (hleft : ∀ a : ℝ, I a ≤ ⨆ b : Set.Iio a, I b) {S : Set ℝ}
    (hS : ∀ a ∉ S, ∃ c, a < c ∧ I c ≤ I a) {r : ℝ} (hr : spectralInvariant I σ = r) : r ∈ S := by
  by_contra hrS
  obtain ⟨c, hrc, hc⟩ := hS r hrS
  have hσ : σ ∈ I r := hc (mem_of_spectralInvariant_lt hI (hr ▸ EReal.coe_lt_coe_iff.2 hrc))
  obtain ⟨⟨b, hb⟩, hσb⟩ := (Submodule.mem_iSup_of_directed _
    (hI.comp (Subtype.mono_coe _)).directed_le).1 (hleft r hσ)
  have := hr ▸ spectralInvariant_le_of_mem hσb
  exact (EReal.coe_le_coe_iff.1 this).not_gt hb

end Module

section ActionFiltration

variable {R : Type*} [Ring R] {X : Type*} [AddCommGroup X] [Module R X] {P : Type*}

/-- The level `a` of the **action filtration** of a family of submodules `V x` indexed by
generators `x` with actions `act x`: the sum of the `V x` over the generators of action below
`a`. For a free module with basis `P`, taking for `V x` the line spanned by `x`, it is the span of
the generators of action below `a`. -/
noncomputable def actionFiltration (V : P → Submodule R X) (act : P → ℝ) (a : ℝ) : Submodule R X :=
  ⨆ (x : P) (_ : act x < a), V x

variable (V : P → Submodule R X) (act : P → ℝ)

/-- A generator of action below `a` lies in the level `a` of the action filtration. -/
theorem le_actionFiltration {x : P} {a : ℝ} (hx : act x < a) : V x ≤ actionFiltration V act a :=
  le_iSup₂_of_le (f := fun x (_ : act x < a) ↦ V x) x hx le_rfl

/-- The level `a` of the action filtration is the least submodule containing the generators of
action below `a`. -/
theorem actionFiltration_le_iff {a : ℝ} {W : Submodule R X} :
    actionFiltration V act a ≤ W ↔ ∀ x, act x < a → V x ≤ W :=
  iSup₂_le_iff

/-- The action filtration is increasing. -/
theorem actionFiltration_mono : Monotone (actionFiltration V act) :=
  fun _ _ hab ↦
    (actionFiltration_le_iff V act).2 fun _ hx ↦ le_actionFiltration V act (hx.trans_le hab)

/-- The action filtration is left continuous: its level `a` is the union of its levels `b < a`. -/
theorem actionFiltration_le_iSup_Iio (a : ℝ) :
    actionFiltration V act a ≤ ⨆ b : Set.Iio a, actionFiltration V act b := by
  refine (actionFiltration_le_iff V act).2 fun x hx ↦ ?_
  refine le_iSup_of_le (⟨(act x + a) / 2, by simp only [Set.mem_Iio]; linarith⟩ : Set.Iio a) ?_
  exact le_actionFiltration V act (by linarith)

/-- At a level below every action the action filtration is zero. -/
theorem actionFiltration_eq_bot {a : ℝ} (ha : ∀ x, a ≤ act x) : actionFiltration V act a = ⊥ :=
  eq_bot_iff.2 ((actionFiltration_le_iff V act).2 fun x hx ↦ ((ha x).not_gt hx).elim)

/-- At a level above every action the action filtration is the sum of all the `V x`. -/
theorem actionFiltration_eq_iSup {a : ℝ} (ha : ∀ x, act x < a) :
    actionFiltration V act a = ⨆ x, V x :=
  le_antisymm ((actionFiltration_le_iff V act).2 fun x _ ↦ le_iSup V x)
    (iSup_le fun x ↦ le_actionFiltration V act (ha x))

/-- The action filtration jumps only at actions: when the set of actions is closed, every level
`a` which is not an action has a level `c > a` where the filtration is the same. -/
theorem exists_lt_actionFiltration_le (hact : IsClosed (Set.range act)) {a : ℝ}
    (ha : a ∉ Set.range act) :
    ∃ c, a < c ∧ actionFiltration V act c ≤ actionFiltration V act a := by
  obtain ⟨c, hac, hc⟩ := exists_Ico_subset_of_mem_nhds (hact.isOpen_compl.mem_nhds ha)
    ⟨a + 1, lt_add_one a⟩
  refine ⟨c, hac, (actionFiltration_le_iff V act).2 fun x hx ↦ le_actionFiltration V act ?_⟩
  by_contra hxa
  exact hc ⟨not_lt.1 hxa, hx⟩ ⟨x, rfl⟩

/-- A linear map carrying each generator into the level of the target action filtration at its
action plus `E` carries every level of the action filtration into the level `E` higher. -/
theorem map_actionFiltration_le {Y : Type*} [AddCommGroup Y] [Module R Y] {Q : Type*}
    (W : Q → Submodule R Y) (act' : Q → ℝ) (f : X →ₗ[R] Y) {E : ℝ}
    (h : ∀ x, (V x).map f ≤ actionFiltration W act' (act x + E)) (a : ℝ) :
    (actionFiltration V act a).map f ≤ actionFiltration W act' (a + E) := by
  refine Submodule.map_le_iff_le_comap.2 ((actionFiltration_le_iff V act).2 fun x hx ↦ ?_)
  refine Submodule.map_le_iff_le_comap.1 ((h x).trans (actionFiltration_mono W act' ?_))
  linarith

end ActionFiltration

section Homology

variable {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat R) c} {n : ι}

/-- **Chain maps shifting the filtration.** If a chain map carries the filtration `F` of the
degree-`n` term of `K` into the filtration `G` of `L` raised by `E`, then it raises the spectral
invariants of degree-`n` homology classes by at most `E`. -/
theorem spectralInvariant_homologyMap_le (φ : K ⟶ L) {F : ℝ → Submodule R (K.X n)}
    {G : ℝ → Submodule R (L.X n)} {E : ℝ} (h : ∀ a, (F a).map (φ.f n).hom ≤ G (a + E))
    (σ : K.homology n) :
    spectralInvariant (fun a ↦ L.moduleCatHomologyImage n (G a)) (homologyMap φ n σ) ≤
      spectralInvariant (fun a ↦ K.moduleCatHomologyImage n (F a)) σ + E :=
  spectralInvariant_map_le (homologyMap φ n).hom (fun a ↦ map_moduleCatHomologyImage_le φ (h a)) σ

variable {P : Type*} (V : P → Submodule R (K.X n)) (act : P → ℝ)

/-- **Spectrality for the action filtration.** If the degree-`n` term of a complex is filtered by
the action filtration of a family of generators whose set of actions is closed, then every finite
spectral invariant of a degree-`n` homology class is the action of a generator. -/
theorem mem_range_of_spectralInvariant_eq_coe (hact : IsClosed (Set.range act))
    {σ : K.homology n} {r : ℝ}
    (hr : spectralInvariant (fun a ↦ K.moduleCatHomologyImage n (actionFiltration V act a)) σ = r) :
    r ∈ Set.range act := by
  have hmono := (moduleCatHomologyImage_mono K n).comp (actionFiltration_mono V act)
  refine mem_of_spectralInvariant_eq_coe hmono (fun a ↦ ?_) (fun a ha ↦ ?_) hr
  · exact moduleCatHomologyImage_le_iSup_Iio (actionFiltration_mono V act)
      (actionFiltration_le_iSup_Iio V act a)
  · obtain ⟨c, hac, hc⟩ := exists_lt_actionFiltration_le V act hact ha
    exact ⟨c, hac, moduleCatHomologyImage_mono K n hc⟩

/-- **Spectrality for finitely many generators.** Let the degree-`n` term of a complex be the sum
of submodules `V x` indexed by finitely many generators `x`, filtered by their actions `act x`.
Then the spectral invariant of every nonzero degree-`n` homology class is the action of a
generator. This is the spectrality of spectral invariants of a nondegenerate Hamiltonian, whose
Floer complex has the `1`-periodic orbits as generators. -/
theorem exists_spectralInvariant_eq [Finite P] (hV : ⨆ x, V x = ⊤) {σ : K.homology n}
    (hσ : σ ≠ 0) :
    ∃ x, spectralInvariant (fun a ↦ K.moduleCatHomologyImage n (actionFiltration V act a)) σ =
      act x := by
  set I := fun a ↦ K.moduleCatHomologyImage n (actionFiltration V act a)
  have hmono : Monotone I := (moduleCatHomologyImage_mono K n).comp (actionFiltration_mono V act)
  obtain ⟨B, hB⟩ := (Set.finite_range act).bddAbove
  obtain ⟨B', hB'⟩ := (Set.finite_range act).bddBelow
  have htop : spectralInvariant I σ ≠ ⊤ := by
    refine (spectralInvariant_le_of_mem (I := I) (a := B + 1) ?_).trans_lt (EReal.coe_lt_top _)
      |>.ne
    have : actionFiltration V act (B + 1) = ⊤ :=
      (actionFiltration_eq_iSup V act fun x ↦ (hB ⟨x, rfl⟩).trans_lt (lt_add_one B)).trans hV
    simp only [I, this, moduleCatHomologyImage_top, Submodule.mem_top]
  have hbot : spectralInvariant I σ ≠ ⊥ := by
    intro h
    have hσB' := (spectralInvariant_eq_bot_iff hmono).1 h B'
    simp only [I, actionFiltration_eq_bot V act fun x ↦ hB' ⟨x, rfl⟩, moduleCatHomologyImage_bot,
      Submodule.mem_bot] at hσB'
    exact hσ hσB'
  obtain ⟨r, hr⟩ : ∃ r : ℝ, spectralInvariant I σ = r :=
    ⟨(spectralInvariant I σ).toReal, (EReal.coe_toReal htop hbot).symm⟩
  obtain ⟨x, hx⟩ := mem_range_of_spectralInvariant_eq_coe V act (Set.finite_range act).isClosed hr
  exact ⟨x, hr.trans (congrArg _ hx.symm)⟩

end Homology

end TauCeti
