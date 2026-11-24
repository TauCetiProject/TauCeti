/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
public import TauCeti.Analysis.CStarAlgebra.Multiplier.Nondegenerate
public import TauCeti.Analysis.CStarAlgebra.Multiplier.Strict.Topology
public import TauCeti.Analysis.CStarAlgebra.Representation.Multiplier
import TauCeti.Analysis.CStarAlgebra.Multiplier.Factorization
import TauCeti.Analysis.CStarAlgebra.Representation.Factorization

/-!
# Strict continuity and Lance–Woronowicz theorem for multiplier extensions

This file establishes the strict-topological functoriality of multiplier algebras of C⋆-algebras
and the global strict-to-strong-star continuity of multiplier extensions of Hilbert-space
representations, following Lance (*Hilbert C\*-Modules*, Proposition 2.5) and Woronowicz.

Using Cohen–Hewitt factorization from `TauCeti.Analysis.CStarAlgebra.Multiplier.Factorization`
(`IsMultiplierNondegenerate.exists_fst_apply_eq`, `exists_snd_apply_eq`) and
`TauCeti.Analysis.CStarAlgebra.Representation.Factorization`
(`coe_essentialSubspace_eq_iUnion_range`), writing `b = (φ a₁).fst y₁` and `b = (φ a₂).snd y₂`
turns the multiplier extension formulas into global identities on all of `B`, yielding:
* global strict continuity and bounded-ball uniqueness of `φ.extendToMultiplierStrict hφ`
  (`continuous_extendToMultiplierStrict`, `eq_extendToMultiplier_of_continuousOn_norm_le`);
* the Lance–Woronowicz equivalence between global strict continuity, unit-ball strict continuity,
  and nondegeneracy on `A` (`StarAlgHom.continuous_conjStarAlgHom_iff_isMultiplierNondegenerate`,
  `StarAlgHom.continuous_conjStarAlgHom_iff_continuousOn_unitBall`);
* global strict-to-strong-star continuity and nondegeneracy characterization for Hilbert-space
  representations (`continuous_strict_nonUnitalMultiplierExtension_apply`,
  `continuous_strict_multiplierExtension_apply`,
  `StarAlgHom.continuous_strict_apply_iff_isNondegenerate`).

## References

* E. C. Lance, *Hilbert C\*-Modules*, London Math. Soc. Lecture Note Series 210, Propositions 1.8
  and 2.5.
* Bruce Blackadar, *Operator Algebras: Theory of C\*-Algebras and von Neumann Algebras*,
  §II.7.3.9–II.7.3.11.
* Iain Raeburn and Dana Williams, *Morita Equivalence and Continuous-Trace C\*-Algebras*,
  Propositions 2.31 and 2.50.
-/

public section

noncomputable section

open Filter Topology
open scoped CStarAlgebra MultiplierAlgebra

/-! ### Strict transport, bounded-ball identity principle, and strict homeomorphisms -/

namespace TauCeti.DoubleCentralizerStrict

section Transport

variable {𝕜 A B C : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜]
  [NonUnitalNormedRing A] [StarRing A] [NormedStarGroup A] [NormedSpace 𝕜 A]
  [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A] [StarModule 𝕜 A]
  [NonUnitalNormedRing B] [StarRing B] [NormedStarGroup B] [NormedSpace 𝕜 B]
  [SMulCommClass 𝕜 B B] [IsScalarTower 𝕜 B B] [StarModule 𝕜 B]
  [NonUnitalNormedRing C] [StarRing C] [NormedStarGroup C] [NormedSpace 𝕜 C]
  [SMulCommClass 𝕜 C C] [IsScalarTower 𝕜 C C] [StarModule 𝕜 C]

/-- View a unital `⋆`-algebra homomorphism `ψ : 𝓜(𝕜, A) →⋆ₐ[𝕜] 𝓜(𝕜, B)` on the strict-topology
copies `𝓜ₛ(𝕜, A) →⋆ₐ[𝕜] 𝓜ₛ(𝕜, B)`. -/
def conjStarAlgHom (ψ : 𝓜(𝕜, A) →⋆ₐ[𝕜] 𝓜(𝕜, B)) : 𝓜ₛ(𝕜, A) →⋆ₐ[𝕜] 𝓜ₛ(𝕜, B) :=
  (starAlgEquiv (𝕜 := 𝕜) (A := B)).symm.toStarAlgHom.comp
    (ψ.comp (starAlgEquiv (𝕜 := 𝕜) (A := A)).toStarAlgHom)

@[simp] theorem toDoubleCentralizer_conjStarAlgHom (ψ : 𝓜(𝕜, A) →⋆ₐ[𝕜] 𝓜(𝕜, B)) (m : 𝓜ₛ(𝕜, A)) :
    (conjStarAlgHom ψ m).toDoubleCentralizer = ψ m.toDoubleCentralizer := (rfl)

@[simp] theorem conjStarAlgHom_ofDoubleCentralizer (ψ : 𝓜(𝕜, A) →⋆ₐ[𝕜] 𝓜(𝕜, B)) (m : 𝓜(𝕜, A)) :
    conjStarAlgHom ψ (ofDoubleCentralizer m) = ofDoubleCentralizer (ψ m) := (rfl)

@[simp] theorem conjStarAlgHom_id :
    conjStarAlgHom (StarAlgHom.id 𝕜 𝓜(𝕜, A)) = StarAlgHom.id 𝕜 𝓜ₛ(𝕜, A) := by
  ext : 1; exact toDoubleCentralizer_injective rfl

@[simp] theorem conjStarAlgHom_comp (ψ₂ : 𝓜(𝕜, B) →⋆ₐ[𝕜] 𝓜(𝕜, C)) (ψ₁ : 𝓜(𝕜, A) →⋆ₐ[𝕜] 𝓜(𝕜, B)) :
    conjStarAlgHom (ψ₂.comp ψ₁) = (conjStarAlgHom ψ₂).comp (conjStarAlgHom ψ₁) := by
  ext : 1; exact toDoubleCentralizer_injective rfl

end Transport

section CStarIso

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- **Bounded-ball strict identity principle.** Two maps from `𝓜ₛ(ℂ, A)` into a Hausdorff space `Y`
that agree on `A` and are continuous on every closed operator-norm ball (`0 ≤ R`) are equal
everywhere on `𝓜ₛ(ℂ, A)`. -/
theorem eq_of_continuousOn_norm_le {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f g : 𝓜ₛ(ℂ, A) → Y} (hcoe : ∀ a : A, f a = g a)
    (hf : ∀ R : ℝ, 0 ≤ R → ContinuousOn f {m | ‖m.toDoubleCentralizer‖ ≤ R})
    (hg : ∀ R : ℝ, 0 ≤ R → ContinuousOn g {m | ‖m.toDoubleCentralizer‖ ≤ R}) : f = g := by
  funext m
  set R := ‖m.toDoubleCentralizer‖
  refine Set.EqOn.of_subset_closure (by rintro _ ⟨a, -, rfl⟩; exact hcoe a)
    (hf R (norm_nonneg _)) (hg R (norm_nonneg _))
    ((closure_image_closedBall (A := A) R).symm ▸ subset_closure)
    (closure_image_closedBall (A := A) R).symm.subset (Set.mem_ofPred.mpr le_rfl)

/-- A `⋆`-algebra isomorphism `e : A ≃⋆ₐ[ℂ] B` of C⋆-algebras induces `𝓜ₛ(ℂ, A) ≃⋆ₐ[ℂ] 𝓜ₛ(ℂ, B)`. -/
def congr (e : A ≃⋆ₐ[ℂ] B) : 𝓜ₛ(ℂ, A) ≃⋆ₐ[ℂ] 𝓜ₛ(ℂ, B) :=
  (starAlgEquiv (𝕜 := ℂ) (A := A)).trans
    ((DoubleCentralizer.congr e).trans (starAlgEquiv (𝕜 := ℂ) (A := B)).symm)

@[simp] theorem toDoubleCentralizer_congr (e : A ≃⋆ₐ[ℂ] B) (m : 𝓜ₛ(ℂ, A)) :
    (congr e m).toDoubleCentralizer = DoubleCentralizer.congr e m.toDoubleCentralizer := (rfl)

@[simp] theorem congr_symm (e : A ≃⋆ₐ[ℂ] B) : (congr e).symm = congr e.symm := by
  ext : 1; exact toDoubleCentralizer_injective (by simp [congr])

@[simp] theorem congr_coe (e : A ≃⋆ₐ[ℂ] B) (a : A) : congr e (a : 𝓜ₛ(ℂ, A)) = (e a : 𝓜ₛ(ℂ, B)) :=
  toDoubleCentralizer_injective (DoubleCentralizer.congr_coe e a)

@[fun_prop] theorem continuous_congr (e : A ≃⋆ₐ[ℂ] B) : Continuous (congr e) :=
  continuous_of_continuous_fst_snd
    (fun b => ((map_continuous e).comp (continuous_fst_apply (e.symm b))).congr fun _ => by simp)
    (fun b => ((map_continuous e).comp (continuous_snd_apply (e.symm b))).congr fun _ => by simp)

/-- A `⋆`-algebra isomorphism `e : A ≃⋆ₐ[ℂ] B` induces a strict uniform equivalence
`𝓜ₛ(ℂ, A) ≃ᵤ 𝓜ₛ(ℂ, B)`. -/
def congrUniformEquiv (e : A ≃⋆ₐ[ℂ] B) : 𝓜ₛ(ℂ, A) ≃ᵤ 𝓜ₛ(ℂ, B) where
  toFun := congr e
  invFun := congr e.symm
  left_inv m := by simp [← congr_symm]
  right_inv m := by simp [← congr_symm]
  uniformContinuous_toFun := uniformContinuous_of_continuousAt_zero
    (congr e).toAddEquiv.toAddMonoidHom (continuous_congr e).continuousAt
  uniformContinuous_invFun := uniformContinuous_of_continuousAt_zero
    (congr e.symm).toAddEquiv.toAddMonoidHom (continuous_congr e.symm).continuousAt

@[simp] theorem coe_congrUniformEquiv (e : A ≃⋆ₐ[ℂ] B) : ⇑(congrUniformEquiv e) = congr e := (rfl)

@[simp] theorem congrUniformEquiv_symm (e : A ≃⋆ₐ[ℂ] B) :
    (congrUniformEquiv e).symm = congrUniformEquiv e.symm := (rfl)

/-- A `⋆`-algebra isomorphism `e : A ≃⋆ₐ[ℂ] B` induces a strict homeomorphism
`𝓜ₛ(ℂ, A) ≃ₜ 𝓜ₛ(ℂ, B)`. -/
def congrHomeomorph (e : A ≃⋆ₐ[ℂ] B) : 𝓜ₛ(ℂ, A) ≃ₜ 𝓜ₛ(ℂ, B) := (congrUniformEquiv e).toHomeomorph

@[simp] theorem coe_congrHomeomorph (e : A ≃⋆ₐ[ℂ] B) : ⇑(congrHomeomorph e) = congr e := (rfl)

@[simp] theorem congrHomeomorph_symm (e : A ≃⋆ₐ[ℂ] B) :
    (congrHomeomorph e).symm = congrHomeomorph e.symm := (rfl)

end CStarIso

end TauCeti.DoubleCentralizerStrict

/-! ### Global strict continuity and Lance–Woronowicz theorem for `extendToMultiplier` -/

namespace NonUnitalStarAlgHom

open TauCeti

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] {φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)}

/-- The unital `⋆`-algebra homomorphism `𝓜ₛ(ℂ, A) →⋆ₐ[ℂ] 𝓜ₛ(ℂ, B)` on strict-topology multiplier
algebras induced by a nondegenerate `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)`. -/
def extendToMultiplierStrict (hφ : φ.IsMultiplierNondegenerate) : 𝓜ₛ(ℂ, A) →⋆ₐ[ℂ] 𝓜ₛ(ℂ, B) :=
  DoubleCentralizerStrict.conjStarAlgHom (φ.extendToMultiplier hφ)

variable (hφ : φ.IsMultiplierNondegenerate)

@[simp] theorem toDoubleCentralizer_extendToMultiplierStrict (m : 𝓜ₛ(ℂ, A)) :
    (φ.extendToMultiplierStrict hφ m).toDoubleCentralizer =
      φ.extendToMultiplier hφ m.toDoubleCentralizer := (rfl)

@[simp] theorem extendToMultiplierStrict_ofDoubleCentralizer (m : 𝓜(ℂ, A)) :
    φ.extendToMultiplierStrict hφ (.ofDoubleCentralizer m) =
      .ofDoubleCentralizer (φ.extendToMultiplier hφ m) := (rfl)

@[simp] theorem extendToMultiplierStrict_coe (a : A) :
    φ.extendToMultiplierStrict hφ (a : 𝓜ₛ(ℂ, A)) = .ofDoubleCentralizer (φ a) :=
  DoubleCentralizerStrict.toDoubleCentralizer_injective (by simp)

@[simp] theorem extendToMultiplierStrict_coeHom
    (h : (DoubleCentralizer.coeHom (𝕜 := ℂ) : A →⋆ₙₐ[ℂ] 𝓜(ℂ, A)).IsMultiplierNondegenerate) :
    (DoubleCentralizer.coeHom (𝕜 := ℂ) : A →⋆ₙₐ[ℂ] 𝓜(ℂ, A)).extendToMultiplierStrict h =
      StarAlgHom.id ℂ 𝓜ₛ(ℂ, A) := by simp [extendToMultiplierStrict]

@[simp] theorem extendToMultiplierStrict_comp {ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)}
    (hψ : ψ.IsMultiplierNondegenerate) :
    ((ψ.extendToMultiplier hψ).toNonUnitalStarAlgHom.comp φ).extendToMultiplierStrict
      (hψ.extendToMultiplier_comp hφ) =
        (ψ.extendToMultiplierStrict hψ).comp (φ.extendToMultiplierStrict hφ) := by
  rw [extendToMultiplierStrict, extendToMultiplier_comp hψ hφ,
    DoubleCentralizerStrict.conjStarAlgHom_comp]; rfl

/-- **Lance's global strict continuity theorem (Lance, Prop. 2.5).** If `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` is
nondegenerate, then `φ.extendToMultiplierStrict hφ : 𝓜ₛ(ℂ, A) →⋆ₐ[ℂ] 𝓜ₛ(ℂ, B)` is globally strictly
continuous (without any norm-boundedness restriction). -/
@[fun_prop] theorem continuous_extendToMultiplierStrict :
    Continuous (φ.extendToMultiplierStrict hφ) := by
  refine DoubleCentralizerStrict.continuous_of_continuous_fst_snd (fun b => ?_) (fun b => ?_)
  · obtain ⟨a, y, rfl⟩ := hφ.exists_fst_apply_eq b
    exact ((((ContinuousLinearMap.apply ℂ B y).continuous.comp
        (continuous_fst.comp DoubleCentralizer.continuous_toProd)).comp
        ((map_continuous φ).comp (DoubleCentralizerStrict.continuous_fst_apply a)))).congr fun m =>
      (φ.extendToMultiplier_fst_apply hφ m.toDoubleCentralizer a y).symm
  · obtain ⟨a, y, rfl⟩ := hφ.exists_snd_apply_eq b
    exact ((((ContinuousLinearMap.apply ℂ B y).continuous.comp
        (continuous_snd.comp DoubleCentralizer.continuous_toProd)).comp
        ((map_continuous φ).comp (DoubleCentralizerStrict.continuous_snd_apply a)))).congr fun m =>
      (φ.extendToMultiplier_snd_apply hφ m.toDoubleCentralizer a y).symm

/-- The unital multiplier extension of a nondegenerate `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` is globally
uniformly continuous for the strict uniformities. -/
theorem uniformContinuous_extendToMultiplierStrict :
    UniformContinuous (φ.extendToMultiplierStrict hφ) :=
  uniformContinuous_of_continuousAt_zero (φ.extendToMultiplierStrict hφ).toAddMonoidHom
    (φ.continuous_extendToMultiplierStrict hφ).continuousAt

/-- Every strict seminorm on `𝓜ₛ(ℂ, B)` pulled back along `φ.extendToMultiplierStrict hφ` is bounded
by finitely many strict seminorms on `𝓜ₛ(ℂ, A)`. -/
theorem isBounded_seminormFamily_extendToMultiplierStrict :
    Seminorm.IsBounded (DoubleCentralizerStrict.seminormFamily ℂ A)
      (DoubleCentralizerStrict.seminormFamily ℂ B)
      (φ.extendToMultiplierStrict hφ).toLinearMap := fun b =>
  let ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous DoubleCentralizerStrict.withSeminorms
    ((DoubleCentralizerStrict.seminormFamily ℂ B b).comp
      (φ.extendToMultiplierStrict hφ).toLinearMap)
    ((DoubleCentralizerStrict.withSeminorms.continuous_seminorm b).comp
      (φ.continuous_extendToMultiplierStrict hφ))
  ⟨s, C, hC⟩

/-- **Bounded-ball strict uniqueness of `extendToMultiplier`.** Any map `f : 𝓜(ℂ, A) → 𝓜(ℂ, B)`
extending `φ` on `A` that is strictly continuous on every closed operator-norm ball (`0 ≤ R`) equals
`φ.extendToMultiplier hφ`. -/
theorem eq_extendToMultiplier_of_continuousOn_norm_le {f : 𝓜(ℂ, A) → 𝓜(ℂ, B)}
    (hf_coe : ∀ a : A, f a = φ a)
    (hf_cont : ∀ R : ℝ, 0 ≤ R → ContinuousOn
      (fun m : 𝓜ₛ(ℂ, A) => DoubleCentralizerStrict.ofDoubleCentralizer (f m.toDoubleCentralizer))
      {m | ‖m.toDoubleCentralizer‖ ≤ R}) : f = φ.extendToMultiplier hφ := by
  have heq := DoubleCentralizerStrict.eq_of_continuousOn_norm_le
    (f := fun m : 𝓜ₛ(ℂ, A) => .ofDoubleCentralizer (f m.toDoubleCentralizer))
    (g := φ.extendToMultiplierStrict hφ) (fun a => by simp [hf_coe a]) hf_cont
    (fun _ _ => (φ.continuous_extendToMultiplierStrict hφ).continuousOn)
  funext m
  exact DoubleCentralizerStrict.ofDoubleCentralizer_injective <| by
    simpa using congrFun heq (.ofDoubleCentralizer m)

end NonUnitalStarAlgHom

namespace StarAlgHom

open TauCeti

section LanceWoronowicz

variable {A B H : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem one_mem_strict_unitBall :
    (1 : 𝓜ₛ(ℂ, A)) ∈ {m : 𝓜ₛ(ℂ, A) | ‖m.toDoubleCentralizer‖ ≤ 1} := by
  simp only [Set.mem_ofPred, DoubleCentralizerStrict.toDoubleCentralizer_one,
    DoubleCentralizer.norm_def, DoubleCentralizer.toProdHom_apply, Prod.norm_def,
    DoubleCentralizer.one_fst, DoubleCentralizer.one_snd, max_self]
  exact ContinuousLinearMap.norm_id_le

private theorem exists_approximateUnit_tendsto_nhdsWithin_unitBall :
    ∃ l : Filter A, l.NeBot ∧ (∀ᶠ e in l, ‖e‖ ≤ 1) ∧ (∀ a : A, Tendsto (· * a) l (𝓝 a)) ∧
      Tendsto (DoubleCentralizerStrict.coe ℂ : A → 𝓜ₛ(ℂ, A)) l
        (𝓝[{m : 𝓜ₛ(ℂ, A) | ‖m.toDoubleCentralizer‖ ≤ 1}] 1) := by
  let := CStarAlgebra.spectralOrder A; have := CStarAlgebra.spectralOrderedRing A
  have hl := CStarAlgebra.increasingApproximateUnit A; have := hl.neBot
  exact ⟨CStarAlgebra.approximateUnit A, hl.neBot, hl.eventually_norm, hl.tendsto_mul_right,
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (DoubleCentralizerStrict.tendsto_coe_one_of_isApproximateUnit hl.toIsApproximateUnit)
      (hl.eventually_norm.mono fun e he => by simpa [Set.mem_ofPred] using he)⟩

private theorem isMultiplierNondegenerate_of_continuousOn_unitBall (ψ : 𝓜(ℂ, A) →⋆ₐ[ℂ] 𝓜(ℂ, B))
    (hψ : ContinuousOn (DoubleCentralizerStrict.conjStarAlgHom ψ)
      {m : 𝓜ₛ(ℂ, A) | ‖m.toDoubleCentralizer‖ ≤ 1}) :
    (ψ.toNonUnitalStarAlgHom.comp DoubleCentralizer.coeHom).IsMultiplierNondegenerate := by
  obtain ⟨l, hl_ne, hl_norm, hl_mul, hl_tendsto⟩ :=
    exists_approximateUnit_tendsto_nhdsWithin_unitBall (A := A)
  rw [(ψ.toNonUnitalStarAlgHom.comp
    DoubleCentralizer.coeHom).isMultiplierNondegenerate_iff_tendsto_fst hl_norm hl_mul]
  intro b
  have hlim := ((DoubleCentralizerStrict.continuous_fst_apply b).tendsto 1).comp <|
    by simpa only [map_one] using (hψ 1 one_mem_strict_unitBall).tendsto.comp hl_tendsto
  simpa only [Function.comp_def, DoubleCentralizerStrict.toDoubleCentralizer_conjStarAlgHom,
    DoubleCentralizerStrict.toDoubleCentralizer_coe,
    DoubleCentralizerStrict.toDoubleCentralizer_one, DoubleCentralizer.one_fst, one_apply_eq_self,
    NonUnitalStarAlgHom.comp_apply, StarAlgHom.coe_toNonUnitalStarAlgHom,
    DoubleCentralizer.coeHom_apply] using hlim

/-- **Lance–Woronowicz theorem.** A unital `⋆`-homomorphism `ψ : 𝓜(ℂ, A) →⋆ₐ[ℂ] 𝓜(ℂ, B)` is
globally strictly continuous if and only if its restriction `ψ ∘ coeHom : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` is
nondegenerate (in which case `ψ` is its canonical multiplier extension). -/
theorem continuous_conjStarAlgHom_iff_isMultiplierNondegenerate (ψ : 𝓜(ℂ, A) →⋆ₐ[ℂ] 𝓜(ℂ, B)) :
    Continuous (DoubleCentralizerStrict.conjStarAlgHom ψ) ↔
      (ψ.toNonUnitalStarAlgHom.comp DoubleCentralizer.coeHom).IsMultiplierNondegenerate := by
  refine ⟨fun hψ => isMultiplierNondegenerate_of_continuousOn_unitBall ψ hψ.continuousOn,
    fun hφ => ?_⟩
  let φ := ψ.toNonUnitalStarAlgHom.comp DoubleCentralizer.coeHom
  have hψ_eq : ψ = φ.extendToMultiplier hφ :=
    StarAlgHom.ext <| congrFun (φ.eq_extendToMultiplier_of_apply_coe hφ ψ fun _ => rfl)
  exact hψ_eq ▸ φ.continuous_extendToMultiplierStrict hφ

/-- A unital `⋆`-homomorphism `ψ : 𝓜(ℂ, A) →⋆ₐ[ℂ] 𝓜(ℂ, B)` is globally strictly continuous if and
only if it is strictly continuous on the closed unit ball of `𝓜ₛ(ℂ, A)`. -/
theorem continuous_conjStarAlgHom_iff_continuousOn_unitBall (ψ : 𝓜(ℂ, A) →⋆ₐ[ℂ] 𝓜(ℂ, B)) :
    Continuous (DoubleCentralizerStrict.conjStarAlgHom ψ) ↔
      ContinuousOn (DoubleCentralizerStrict.conjStarAlgHom ψ)
        {m : 𝓜ₛ(ℂ, A) | ‖m.toDoubleCentralizer‖ ≤ 1} :=
  ⟨Continuous.continuousOn, fun h => (ψ.continuous_conjStarAlgHom_iff_isMultiplierNondegenerate).2
    (isMultiplierNondegenerate_of_continuousOn_unitBall ψ h)⟩

/-- A unital `⋆`-homomorphism `ψ : 𝓜(ℂ, A) →⋆ₐ[ℂ] 𝓜(ℂ, B)` is globally strictly continuous if and
only if it is strictly continuous on every closed operator-norm ball (`0 ≤ R`). -/
theorem continuous_conjStarAlgHom_iff_continuousOn_norm_le (ψ : 𝓜(ℂ, A) →⋆ₐ[ℂ] 𝓜(ℂ, B)) :
    Continuous (DoubleCentralizerStrict.conjStarAlgHom ψ) ↔
      ∀ R : ℝ, 0 ≤ R → ContinuousOn (DoubleCentralizerStrict.conjStarAlgHom ψ)
        {m : 𝓜ₛ(ℂ, A) | ‖m.toDoubleCentralizer‖ ≤ R} :=
  ⟨fun h _ _ => h.continuousOn, fun h =>
    (ψ.continuous_conjStarAlgHom_iff_continuousOn_unitBall).2 (h 1 zero_le_one)⟩

end LanceWoronowicz

end StarAlgHom

/-! ### Global strict-to-strong-star continuity of Hilbert-space multiplier extensions -/

namespace NonUnitalStarAlgHom

open TauCeti

variable {A H : Type*} [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Global strict-to-strong continuity of `nonUnitalMultiplierExtension`.** For any (possibly
degenerate) Hilbert-space representation `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` and any `ξ : H`, the map
`m ↦ π.nonUnitalMultiplierExtension m.toDoubleCentralizer ξ` is globally continuous on `𝓜ₛ(ℂ, A)`
(without any norm-boundedness restriction). -/
@[fun_prop] theorem continuous_strict_nonUnitalMultiplierExtension_apply (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (ξ : H) :
    Continuous fun m : 𝓜ₛ(ℂ, A) => π.nonUnitalMultiplierExtension m.toDoubleCentralizer ξ := by
  have hmem : (π.essentialSubspace.starProjection ξ : H) ∈ ⋃ a, Set.range (π a) :=
    π.coe_essentialSubspace_eq_iUnion_range ▸
      Submodule.starProjection_apply_mem π.essentialSubspace ξ
  obtain ⟨a, η, hη⟩ := Set.mem_iUnion.1 hmem
  refine (((ContinuousLinearMap.apply ℂ H η).continuous.comp (map_continuous π)).comp
    (DoubleCentralizerStrict.continuous_fst_apply a)).congr fun m => ?_
  calc π (m.toDoubleCentralizer.fst a) η
      = π.nonUnitalMultiplierExtension m.toDoubleCentralizer (π a η) +
          π.nonUnitalMultiplierExtension m.toDoubleCentralizer
            (ξ - π.essentialSubspace.starProjection ξ) := by
        rw [π.nonUnitalMultiplierExtension_apply_apply,
          π.nonUnitalMultiplierExtension_apply_eq_zero _
            (π.essentialSubspace.sub_starProjection_mem_orthogonal ξ), add_zero]
    _ = π.nonUnitalMultiplierExtension m.toDoubleCentralizer ξ := by
        rw [hη, ← map_add, add_sub_cancel]

/-- **Global strict-to-strong-star continuity of `nonUnitalMultiplierExtension`.** For any
Hilbert-space representation `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` and any `ξ : H`, the adjoint evaluation
`m ↦ star (π.nonUnitalMultiplierExtension m.toDoubleCentralizer) ξ` is globally continuous on
`𝓜ₛ(ℂ, A)`. -/
@[fun_prop] theorem continuous_strict_star_nonUnitalMultiplierExtension_apply
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    Continuous fun m : 𝓜ₛ(ℂ, A) =>
      star (π.nonUnitalMultiplierExtension m.toDoubleCentralizer) ξ :=
  ((π.continuous_strict_nonUnitalMultiplierExtension_apply ξ).comp continuous_star).congr
    fun _ => by simp [map_star]

/-- `π.nonUnitalMultiplierExtension` is globally continuous from `𝓜ₛ(ℂ, A)` into `H →Lₚₜ[ℂ] H`
(the strong operator topology). -/
theorem continuous_strict_toPointwiseConvergenceCLM_nonUnitalMultiplierExtension
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    Continuous fun m : 𝓜ₛ(ℂ, A) => ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
      H H (π.nonUnitalMultiplierExtension m.toDoubleCentralizer) :=
  PointwiseConvergenceCLM.continuous_of_continuous_eval
    π.continuous_strict_nonUnitalMultiplierExtension_apply

section Nondegenerate

variable {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hπ : π.IsNondegenerate)

/-- **Global strict-to-strong continuity of `multiplierExtension`.** If `π` is nondegenerate, then
`m ↦ π.multiplierExtension hπ m.toDoubleCentralizer ξ` is globally continuous on `𝓜ₛ(ℂ, A)` for
every `ξ : H`. -/
@[fun_prop] theorem continuous_strict_multiplierExtension_apply (ξ : H) :
    Continuous fun m : 𝓜ₛ(ℂ, A) => π.multiplierExtension hπ m.toDoubleCentralizer ξ :=
  (π.continuous_strict_nonUnitalMultiplierExtension_apply ξ).congr fun m =>
    congr($(π.nonUnitalMultiplierExtension_eq_multiplierExtension hπ m.toDoubleCentralizer) ξ)

/-- **Global strict-to-strong-star continuity of `multiplierExtension`.** If `π` is nondegenerate,
then `m ↦ star (π.multiplierExtension hπ m.toDoubleCentralizer) ξ` is globally continuous on
`𝓜ₛ(ℂ, A)` for every `ξ : H`. -/
@[fun_prop] theorem continuous_strict_star_multiplierExtension_apply (ξ : H) :
    Continuous fun m : 𝓜ₛ(ℂ, A) => star (π.multiplierExtension hπ m.toDoubleCentralizer) ξ :=
  ((continuous_strict_multiplierExtension_apply hπ ξ).comp continuous_star).congr fun _ => by
    simp [map_star]

/-- If `π` is nondegenerate, `π.multiplierExtension hπ` is globally continuous from `𝓜ₛ(ℂ, A)` into
`H →Lₚₜ[ℂ] H` (the strong operator topology). -/
theorem continuous_strict_toPointwiseConvergenceCLM_multiplierExtension :
    Continuous fun m : 𝓜ₛ(ℂ, A) => ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
      H H (π.multiplierExtension hπ m.toDoubleCentralizer) :=
  PointwiseConvergenceCLM.continuous_of_continuous_eval
    (continuous_strict_multiplierExtension_apply hπ)

/-- **Bounded-ball strong uniqueness of `multiplierExtension`.** Any map `f : 𝓜(ℂ, A) → (H →L[ℂ] H)`
extending `π` on `A` that is strictly-to-strongly continuous on every closed operator-norm ball
(`0 ≤ R`) equals `π.multiplierExtension hπ`. -/
theorem eq_multiplierExtension_of_continuousOn_norm_le {f : 𝓜(ℂ, A) → (H →L[ℂ] H)}
    (hf_coe : ∀ a : A, f a = π a)
    (hf_cont : ∀ R : ℝ, 0 ≤ R → ∀ ξ : H, ContinuousOn
      (fun m : 𝓜ₛ(ℂ, A) => f m.toDoubleCentralizer ξ) {m | ‖m.toDoubleCentralizer‖ ≤ R}) :
    f = π.multiplierExtension hπ := by
  funext m; ext ξ
  exact congrFun (DoubleCentralizerStrict.eq_of_continuousOn_norm_le
    (f := fun x : 𝓜ₛ(ℂ, A) => f x.toDoubleCentralizer ξ)
    (g := fun x : 𝓜ₛ(ℂ, A) => π.multiplierExtension hπ x.toDoubleCentralizer ξ)
    (fun a => by simp [hf_coe a]) (fun R hR => hf_cont R hR ξ)
    (fun _ _ => (continuous_strict_multiplierExtension_apply hπ ξ).continuousOn))
    (.ofDoubleCentralizer m)

end Nondegenerate

end NonUnitalStarAlgHom

namespace StarAlgHom

open TauCeti

variable {A H : Type*} [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem isNondegenerate_of_continuousOn_strict_unitBall (ρ : 𝓜(ℂ, A) →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hρ : ∀ ξ : H, ContinuousOn (fun m : 𝓜ₛ(ℂ, A) => ρ m.toDoubleCentralizer ξ)
      {m : 𝓜ₛ(ℂ, A) | ‖m.toDoubleCentralizer‖ ≤ 1}) :
    (ρ.toNonUnitalStarAlgHom.comp DoubleCentralizer.coeHom).IsNondegenerate := by
  obtain ⟨l, hl_ne, hl_norm, hl_mul, hl_tendsto⟩ :=
    exists_approximateUnit_tendsto_nhdsWithin_unitBall (A := A)
  rw [(ρ.toNonUnitalStarAlgHom.comp DoubleCentralizer.coeHom).isNondegenerate_iff_tendsto
    hl_norm hl_mul]
  intro ξ
  simpa only [Function.comp_def, DoubleCentralizerStrict.toDoubleCentralizer_coe,
    DoubleCentralizerStrict.toDoubleCentralizer_one, map_one, one_apply_eq_self,
    NonUnitalStarAlgHom.comp_apply, StarAlgHom.coe_toNonUnitalStarAlgHom,
    DoubleCentralizer.coeHom_apply] using (hρ ξ 1 one_mem_strict_unitBall).tendsto.comp hl_tendsto

/-- A unital representation `ρ : 𝓜(ℂ, A) →⋆ₐ[ℂ] (H →L[ℂ] H)` is globally strictly-to-strongly
continuous if and only if its restriction to `A` is nondegenerate (in which case `ρ` is the
canonical multiplier extension of `ρ|_A`). -/
theorem continuous_strict_apply_iff_isNondegenerate (ρ : 𝓜(ℂ, A) →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    (∀ ξ : H, Continuous fun m : 𝓜ₛ(ℂ, A) => ρ m.toDoubleCentralizer ξ) ↔
      (ρ.toNonUnitalStarAlgHom.comp DoubleCentralizer.coeHom).IsNondegenerate := by
  refine ⟨fun hρ => isNondegenerate_of_continuousOn_strict_unitBall ρ fun ξ => (hρ ξ).continuousOn,
    fun hπ ξ => ?_⟩
  let π := ρ.toNonUnitalStarAlgHom.comp DoubleCentralizer.coeHom
  have hρ_eq : ρ = π.multiplierExtension hπ :=
    StarAlgHom.ext <| congrFun (π.eq_multiplierExtension_of_apply_coe hπ ρ fun _ => rfl)
  exact hρ_eq ▸ π.continuous_strict_multiplierExtension_apply hπ ξ

/-- A unital representation `ρ : 𝓜(ℂ, A) →⋆ₐ[ℂ] (H →L[ℂ] H)` is globally strictly-to-strongly
continuous if and only if it is strictly-to-strongly continuous on the closed unit ball of
`𝓜ₛ(ℂ, A)`. -/
theorem continuous_strict_apply_iff_continuousOn_unitBall (ρ : 𝓜(ℂ, A) →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    (∀ ξ : H, Continuous fun m : 𝓜ₛ(ℂ, A) => ρ m.toDoubleCentralizer ξ) ↔
      ∀ ξ : H, ContinuousOn (fun m : 𝓜ₛ(ℂ, A) => ρ m.toDoubleCentralizer ξ)
        {m : 𝓜ₛ(ℂ, A) | ‖m.toDoubleCentralizer‖ ≤ 1} :=
  ⟨fun h ξ => (h ξ).continuousOn, fun h =>
    (ρ.continuous_strict_apply_iff_isNondegenerate).2
      (isNondegenerate_of_continuousOn_strict_unitBall ρ h)⟩

end StarAlgHom
