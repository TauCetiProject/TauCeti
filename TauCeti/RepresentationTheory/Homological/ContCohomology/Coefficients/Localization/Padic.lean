/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import TauCeti.NumberTheory.Padics.ContinuousMapLattice
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coefficients.Localization.Basic
import TauCeti.Algebra.Module.LocalizedModule.Kernel
import TauCeti.RingTheory.TensorProduct.IsBaseChange

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
  `s ∈ ℤ_p` kills it (`IsLocalizedModule.exists_mem_smul_eq_zero_of_mem_ker`);
* a `ℚ_p`-basis of `V` scaled into the image of `ι` spans an open `ℤ_p`-lattice `W`, and lifting
  the basis vectors to `T` gives a continuous section of `ι` over `W`
  (`TauCeti.ContinuousCohomology.exists_isOpen_section_of_bijective`);
* a nonzero `s ∈ ℤ_p` acts on `V` invertibly, with inverse the morphism `s⁻¹ • -`
  (`TauCeti.ContinuousCohomology.exists_smul_eq_id`).

## Main results

* `TauCeti.ContinuousCohomology.isLocalizedModule_coeffMap_of_bijective`:
  `Hⁿ(G, T) → Hⁿ(G, V)` is a localization at the nonzero divisors of `ℤ_p`.
* `TauCeti.ContinuousCohomology.rationalizationEquiv`: the resulting `ℤ_p`-linear isomorphism
  `ℚ_p ⊗[ℤ_p] Hⁿ(G, T) ≃ Hⁿ(G, V)`, with `rationalizationEquiv_one_tmul` identifying it with the
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
    (IsBaseChange.iff_liftBaseChange_bijective.2 hι)

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
  have hW : IsOpen (W : Set V) := b'.isOpen_span_padicInt_of_continuous_coord hcont
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
  rw [ContinuousMap.coe_mk, map_sum]
  conv_rhs => rw [← b'.sum_repr w]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [_root_.map_smul, ← hb', ← algebraMap_smul ℚ_[p], PadicInt.algebraMap_apply]

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

/-- **Lattice cohomology localizes.** Let `G` be a compact group, `T` a finitely generated
`ℤ_p`-module, `V` a `ℚ_p`-module carrying its `ℚ_p`-module topology (`IsModuleTopology ℚ_[p] V`),
and `ι : T ⟶ V` with `ℚ_p ⊗ T → V` bijective. Then the map `Hⁿ(G, T) → Hⁿ(G, V)` induced by `ι`
is a localization at the nonzero divisors of `ℤ_p`. -/
theorem isLocalizedModule_coeffMap_of_bijective (n : ℕ) :
    IsLocalizedModule (nonZeroDivisors ℤ_[p]) (coeffMap ι n).hom.toLinearMap := by
  have := isLocalizedModule_of_bijective hι
  obtain ⟨s, hs, hker⟩ :=
    IsLocalizedModule.exists_mem_smul_eq_zero_of_mem_ker (nonZeroDivisors ℤ_[p]) ι.hom.toLinearMap
  obtain ⟨W, hW, habs, σ, hσ⟩ := exists_isOpen_section_of_bijective hι
  exact isLocalizedModule_coeffMap ⟨s, hs, fun a ha ↦ hker a ha⟩
    (exists_map_eq_smul_of_isOpen W hW habs σ hσ)
    (fun _ hs ↦ exists_smul_eq_id hs) n

/-- **Rationalisation of lattice cohomology** (Rubin, *Euler Systems*, Appendix B, §2,
Proposition 2.4). For a compact group `G`, a finitely generated `ℤ_p`-module `T`, a
`ℚ_p`-module `V` carrying its `ℚ_p`-module topology (`IsModuleTopology ℚ_[p] V`) and
`ι : T ⟶ V` with `ℚ_p ⊗ T → V` bijective, `ℚ_p ⊗[ℤ_p] Hⁿ(G, T) ≃ Hⁿ(G, V)`. -/
noncomputable def rationalizationEquiv (n : ℕ) :
    ℚ_[p] ⊗[ℤ_[p]] continuousCohomology n T ≃ₗ[ℤ_[p]] continuousCohomology n V :=
  haveI := isLocalizedModule_coeffMap_of_bijective hι n
  IsLocalizedModule.linearEquiv (nonZeroDivisors ℤ_[p])
    (TensorProduct.mk ℤ_[p] ℚ_[p] (continuousCohomology n T) 1) (coeffMap ι n).hom.toLinearMap

/-- `rationalizationEquiv` sends `1 ⊗ x` to the image of `x` under the map induced by `ι`. -/
@[simp]
theorem rationalizationEquiv_one_tmul (n : ℕ) (x : continuousCohomology n T) :
    rationalizationEquiv hι n (1 ⊗ₜ x) = (coeffMap ι n).hom x :=
  haveI := isLocalizedModule_coeffMap_of_bijective hι n
  IsLocalizedModule.linearEquiv_apply (nonZeroDivisors ℤ_[p])
    (TensorProduct.mk ℤ_[p] ℚ_[p] (continuousCohomology n T) 1) _ x

end TauCeti.ContinuousCohomology
