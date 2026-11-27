/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import TauCeti.NumberTheory.Padics.ContinuousMapLattice
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Localization.Basic

/-!
# Rationalisation of lattice cohomology

Let `G` be a compact group, `T` a finitely generated topological `ℤ_p`-module with a continuous
`G`-action, and `V = T ⊗ ℚ_p`, a topological `ℚ_p`-vector space with its module topology,
presented by a morphism `ι : T ⟶ V` of topological representations whose scalar
extension `ℚ_p ⊗ T → V` is bijective. Then `ι` induces an isomorphism
`ℚ_p ⊗[ℤ_p] Hⁿ(G, T) ≅ Hⁿ(G, V)` in every degree (Rubin, *Euler Systems*, Appendix B, §2,
Proposition 2.4). Torsion in `T` is allowed.

This is `TauCeti.ContinuousCohomology.isLocalizedModule_coeffMap` for the submonoid of nonzero
divisors of `ℤ_p`, once its three hypotheses are checked for `ι`:

* the kernel of `ι` is the torsion submodule of `T`, finitely generated, so a single nonzero
  `s ∈ ℤ_p` kills it (`TauCeti.ContinuousCohomology.exists_smul_eq_zero_of_bijective`);
* a `ℚ_p`-basis of `V` scaled into the image of `ι` spans an open `ℤ_p`-lattice `W`, and lifting
  the basis vectors to `T` gives a continuous section of `ι` over `W`
  (`TauCeti.ContinuousCohomology.exists_isOpen_section_of_bijective`);
* a nonzero `s ∈ ℤ_p` acts on `V` invertibly, with inverse the morphism `s⁻¹ • -`
  (`TauCeti.ContinuousCohomology.exists_smul_eq_id`).

## Main results

* `TauCeti.ContinuousCohomology.isLocalizedModule_coeffMap_of_bijective`:
  `Hⁿ(G, T) → Hⁿ(G, V)` is a localization at the nonzero divisors of `ℤ_p`.
* `TauCeti.ContinuousCohomology.rationalisationEquiv`: the resulting `ℤ_p`-linear isomorphism
  `ℚ_p ⊗[ℤ_p] Hⁿ(G, T) ≃ Hⁿ(G, V)`, with `rationalisationEquiv_one_tmul` identifying it with the
  map induced by `ι` on `1 ⊗ x`.

## References

* K. Rubin, *Euler Systems*, Appendix B, §2, Proposition 2.4.
-/

public section

open CategoryTheory TopRep
open scoped TensorProduct

namespace TauCeti.ContinuousCohomology

universe v

variable {p : ℕ} [Fact p.Prime] {G : Type v} [Group G] {T V : TopRep.{v} ℤ_[p] G}
  [Module ℚ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V] {ι : T ⟶ V}

/-- A morphism whose scalar extension to `ℚ_p` is bijective is a localization at the nonzero
divisors of `ℤ_p`. -/
private theorem isLocalizedModule_of_bijective
    (hι : Function.Bijective (ι.hom.toLinearMap.liftBaseChange ℚ_[p])) :
    IsLocalizedModule (nonZeroDivisors ℤ_[p]) ι.hom.toLinearMap :=
  (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ_[p]) ℚ_[p] _).2
    (IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hι) fun x ↦ by simp)

/-- **The kernel of `T → V` is killed by one scalar.** If `T` is finitely generated and
`ℚ_p ⊗ T → V` is bijective, one nonzero `s ∈ ℤ_p` kills every element of `T` mapping to zero. -/
theorem exists_smul_eq_zero_of_bijective [Module.Finite ℤ_[p] T]
    (hι : Function.Bijective (ι.hom.toLinearMap.liftBaseChange ℚ_[p])) :
    ∃ s ∈ nonZeroDivisors ℤ_[p], ∀ a, ι.hom a = 0 → s • a = 0 := by
  classical
  have := isLocalizedModule_of_bijective hι
  obtain ⟨F, hF⟩ := IsNoetherian.noetherian (LinearMap.ker ι.hom.toLinearMap)
  have hc : ∀ a : T.V, ∃ c : nonZeroDivisors ℤ_[p], ι.hom a = 0 → (c : ℤ_[p]) • a = 0 :=
    fun a ↦ by
      by_cases ha : ι.hom a = 0
      · obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors ℤ_[p])
          (f := ι.hom.toLinearMap) (x₁ := a) (x₂ := 0) (by rw [_root_.map_zero]; exact ha)
        exact ⟨c, fun _ ↦ hc.trans (smul_zero c)⟩
      · exact ⟨1, fun h ↦ absurd h ha⟩
  choose c hc using hc
  refine ⟨∏ a ∈ F, (c a : ℤ_[p]), Submonoid.prod_mem _ fun a _ ↦ (c a).property,
    fun a ha ↦ ?_⟩
  have hmem : a ∈ Submodule.span ℤ_[p] (F : Set T.V) := hF ▸ LinearMap.mem_ker.2 ha
  clear ha
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul _ _ hx, mul_smul,
      hc x (LinearMap.mem_ker.1 (hF ▸ Submodule.subset_span hx)), smul_zero]
  | zero => exact smul_zero _
  | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
  | smul r x _ hx => rw [smul_comm, hx, smul_zero]

variable [IsModuleTopology ℚ_[p] V]

/-- **An open lattice with a continuous section.** If `T` is finitely generated, `V` carries its
`ℚ_p`-module topology and `ℚ_p ⊗ T → V` is bijective, then some open
`ℤ_p`-submodule `W` of `V`, absorbing `V` along the nonzero divisors, has a continuous map
`σ : W → T` with `ι ∘ σ = id`. -/
theorem exists_isOpen_section_of_bijective [Module.Finite ℤ_[p] T]
    (hι : Function.Bijective (ι.hom.toLinearMap.liftBaseChange ℚ_[p])) :
    ∃ W : Submodule ℤ_[p] V, IsOpen (W : Set V) ∧ (∀ v, ∃ s ∈ nonZeroDivisors ℤ_[p], s • v ∈ W) ∧
      ∃ σ : C(W, T), ∀ w, ι.hom (σ w) = w := by
  have := isLocalizedModule_of_bijective hι
  have : Module.Finite ℚ_[p] V := Module.Finite.of_surjective _ hι.2
  let b := Module.finBasis ℚ_[p] V
  -- scale the basis into the image of `ι`
  have hsurj : ∀ i, ∃ x : T × nonZeroDivisors ℤ_[p], x.2 • b i = ι.hom x.1 := fun i ↦
    IsLocalizedModule.surj (nonZeroDivisors ℤ_[p]) ι.hom.toLinearMap (b i)
  choose x hx using hsurj
  have hu : ∀ i, IsUnit (algebraMap ℤ_[p] ℚ_[p] (x i).2) := fun i ↦
    IsLocalization.map_units ℚ_[p] (x i).2
  let b' := b.unitsSMul fun i ↦ (hu i).unit
  have hb' : ∀ i, b' i = ι.hom (x i).1 := fun i ↦ by
    rw [Module.Basis.unitsSMul_apply, Units.smul_def, IsUnit.unit_spec, algebraMap_smul]
    exact hx i
  let W : Submodule ℤ_[p] V := Submodule.span ℤ_[p] (Set.range b')
  have hcont : ∀ i, Continuous (b'.coord i) := fun i ↦
    IsModuleTopology.continuous_of_linearMap _
  have hW : IsOpen (W : Set V) := by
    have h : (W : Set V) = ⋂ i, (b'.coord i) ⁻¹' Metric.closedBall 0 1 := by
      ext v
      simp [W, Module.Basis.mem_span_padicInt_iff_norm_repr_le_one]
    rw [h]
    exact isOpen_iInter_of_finite fun i ↦
      (IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero).preimage (hcont i)
  have hp : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨W, hW, fun v ↦ ?_, ?_⟩
  · obtain ⟨n, hn⟩ := exists_padicInt_pow_smul_mem hW v
    exact ⟨_, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hp), hn⟩
  have hle : ∀ (w : W) i, ‖b'.repr w i‖ ≤ 1 := fun w ↦
    (Module.Basis.mem_span_padicInt_iff_norm_repr_le_one b' w).1 w.property
  let c : W → Fin (Module.finrank ℚ_[p] V) → ℤ_[p] := fun w i ↦ ⟨b'.repr w i, hle w i⟩
  have hc : ∀ i, Continuous fun w ↦ c w i := fun i ↦
    ((hcont i).comp continuous_subtypeVal).subtype_mk _
  refine ⟨⟨fun w ↦ ∑ i, c w i • (x i).1,
    continuous_finsetSum _ fun i _ ↦ (hc i).smul continuous_const⟩, fun w ↦ ?_⟩
  change ι.hom (∑ i, c w i • (x i).1) = w
  rw [map_sum]
  conv_rhs => rw [← b'.sum_repr w]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [_root_.map_smul, ← hb', ← algebraMap_smul ℚ_[p]]
  rfl

omit [IsModuleTopology ℚ_[p] V] in
/-- **Nonzero scalars act invertibly on `V`.** For a nonzero `s ∈ ℤ_p`, multiplication by
`s⁻¹ ∈ ℚ_p` is a morphism `u` of topological representations with `s • u = 𝟙 V`. -/
theorem exists_smul_eq_id [ContinuousConstSMul ℚ_[p] V] {s : ℤ_[p]}
    (hs : s ∈ nonZeroDivisors ℤ_[p]) : ∃ u : V ⟶ V, s • u = 𝟙 V := by
  have hs' : algebraMap ℤ_[p] ℚ_[p] s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  set q := (algebraMap ℤ_[p] ℚ_[p] s)⁻¹
  have hsq : ∀ v : V, s • q • v = v := fun v ↦ by
    rw [← algebraMap_smul ℚ_[p] s, smul_smul, mul_inv_cancel₀ hs', one_smul]
  refine ⟨TopRep.ofHom
    { toFun v := q • v
      map_add' := smul_add q
      map_smul' c v := smul_comm q c v
      isIntertwining' g := by
        ext v
        -- both sides are the unique `w` with `s • w = V.ρ g v`
        refine smul_right_injective V hs' ?_
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_mk',
          LinearMap.coe_mk, AddHom.coe_mk, algebraMap_smul]
        rw [hsq, ← ContinuousLinearMap.map_smul, hsq]
      cont := continuous_const_smul q }, ?_⟩
  ext v
  exact hsq v

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [Module.Finite ℤ_[p] T]
  (hι : Function.Bijective (ι.hom.toLinearMap.liftBaseChange ℚ_[p]))
include hι

/-- **Lattice cohomology localizes.** For a compact group `G`, the map `Hⁿ(G, T) → Hⁿ(G, V)`
induced by `ι` is a localization at the nonzero divisors of `ℤ_p`. -/
theorem isLocalizedModule_coeffMap_of_bijective (n : ℕ) :
    IsLocalizedModule (nonZeroDivisors ℤ_[p]) (coeffMap ι n).hom.toLinearMap := by
  obtain ⟨W, hW, habs, σ, hσ⟩ := exists_isOpen_section_of_bijective hι
  exact isLocalizedModule_coeffMap (exists_smul_eq_zero_of_bijective hι)
    (lift_of_isOpen W hW habs σ hσ)
    (fun _ hs ↦ exists_smul_eq_id hs) n

/-- **Rationalisation of lattice cohomology** (Rubin, *Euler Systems*, Appendix B, §2,
Proposition 2.4). For a compact group `G`, a finitely generated `ℤ_p`-module `T` and
`ι : T ⟶ V` with `ℚ_p ⊗ T → V` bijective, `ℚ_p ⊗[ℤ_p] Hⁿ(G, T) ≃ Hⁿ(G, V)`. -/
noncomputable def rationalisationEquiv (n : ℕ) :
    ℚ_[p] ⊗[ℤ_[p]] continuousCohomology n T ≃ₗ[ℤ_[p]] continuousCohomology n V :=
  haveI := isLocalizedModule_coeffMap_of_bijective hι n
  IsLocalizedModule.linearEquiv (nonZeroDivisors ℤ_[p])
    (TensorProduct.mk ℤ_[p] ℚ_[p] (continuousCohomology n T) 1) (coeffMap ι n).hom.toLinearMap

/-- `rationalisationEquiv` sends `1 ⊗ x` to the image of `x` under the map induced by `ι`. -/
@[simp]
theorem rationalisationEquiv_one_tmul (n : ℕ) (x : continuousCohomology n T) :
    rationalisationEquiv hι n (1 ⊗ₜ x) = (coeffMap ι n).hom x :=
  haveI := isLocalizedModule_coeffMap_of_bijective hι n
  IsLocalizedModule.linearEquiv_apply (nonZeroDivisors ℤ_[p])
    (TensorProduct.mk ℤ_[p] ℚ_[p] (continuousCohomology n T) 1) _ x

end TauCeti.ContinuousCohomology
