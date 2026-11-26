/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.AsymptoticMorphism.Basic
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Path
import TauCeti.Topology.ContinuousMap.Star

/-!
# Homotopy of asymptotic morphisms

Two asymptotic morphisms `φ, ψ : AsymptoticMorphism A B` between (possibly nonunital) C⋆-algebras
are *homotopic* if they are the endpoints `s = 0` and `s = 1` of a single asymptotic morphism
`H : AsymptoticMorphism A C(unitInterval, B)` into the path C⋆-algebra `C([0, 1], B)` (Blackadar,
*K-Theory for Operator Algebras*, Definition 25.1.2). Because the norm on `C(unitInterval, B)` is
the supremum norm over `s ∈ [0, 1]`, the asymptotic algebra defects of `H` tend to `0` uniformly in
the homotopy parameter `s`.

## Main definitions and results

* `TauCeti.AsymptoticMorphism.evalAt` and `TauCeti.AsymptoticMorphism.Homotopic`: endpoint
  evaluation on `C(unitInterval, B)` and homotopy of asymptotic morphisms.
* `TauCeti.AsymptoticMorphism.Homotopic.refl`, `TauCeti.AsymptoticMorphism.Homotopic.symm`,
  `TauCeti.AsymptoticMorphism.Homotopic.trans`, and `TauCeti.AsymptoticMorphism.homotopySetoid`:
  homotopy of asymptotic morphisms is an equivalence relation.
* `TauCeti.AsymptoticMorphism.Equiv.homotopic`: asymptotically equivalent asymptotic morphisms are
  homotopic via straight-line interpolation.
* `TauCeti.AsymptoticMorphism.Homotopic.compStarAlgHom` and
  `TauCeti.AsymptoticMorphism.Homotopic.postcompStarAlgHom`: functoriality of homotopy under
  pre- and post-composition with `⋆`-homomorphisms.
* `TauCeti.AsymptoticMorphism.homotopic_reparam`: every asymptotic morphism is homotopic to any
  continuous reparameterization `r : C(Set.Ici 1, Set.Ici 1)` tending to `∞` (Blackadar,
  Proposition 25.1.5).
* `TauCeti.AsymptoticHomotopy`: the set `[[A, B]]` of homotopy classes of asymptotic morphisms from
  `A` to `B`.

## References

* Alain Connes and Nigel Higson, *Déformations, morphismes asymptotiques et K-théorie bivariante*,
  C. R. Acad. Sci. Paris Sér. I Math. **311** (1990), no. 2, 101–106.
* Bruce Blackadar, *K-Theory for Operator Algebras*, 2nd ed., MSRI Publications **5**, Cambridge
  University Press, 1998, §25.1 (Definition 25.1.2, Proposition 25.1.5).
-/

public section

open Filter Set Topology unitInterval
open scoped BoundedContinuousFunction CStarAlgebra

namespace TauCeti

namespace AsymptoticMorphism

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C]

/-- Evaluate an asymptotic morphism into the path C⋆-algebra `C(unitInterval, B)` at a parameter
`s : unitInterval`. -/
noncomputable def evalAt (H : AsymptoticMorphism A C(unitInterval, B)) (s : unitInterval) :
    AsymptoticMorphism A B :=
  H.postcompStarAlgHom (ContinuousMap.evalNonUnitalStarAlgHom ℂ B s)

@[simp]
theorem evalAt_apply (H : AsymptoticMorphism A C(unitInterval, B)) (s : unitInterval)
    (t : Ici (1 : ℝ)) (a : A) : H.evalAt s t a = H t a s := by simp [evalAt]

/-- Two asymptotic morphisms `φ, ψ : AsymptoticMorphism A B` are *homotopic* if there exists an
asymptotic morphism `H : AsymptoticMorphism A C(unitInterval, B)` with `H.evalAt 0 = φ` and
`H.evalAt 1 = ψ`. -/
def Homotopic (φ ψ : AsymptoticMorphism A B) : Prop :=
  ∃ H : AsymptoticMorphism A C(unitInterval, B), H.evalAt 0 = φ ∧ H.evalAt 1 = ψ

theorem homotopic_def {φ ψ : AsymptoticMorphism A B} :
    φ.Homotopic ψ ↔
      ∃ H : AsymptoticMorphism A C(unitInterval, B), H.evalAt 0 = φ ∧ H.evalAt 1 = ψ := Iff.rfl

@[refl]
theorem Homotopic.refl (φ : AsymptoticMorphism A B) : φ.Homotopic φ :=
  ⟨φ.postcompStarAlgHom (ContinuousMap.constNonUnitalStarAlgHom ℂ unitInterval B),
    by ext; simp, by ext; simp⟩

@[symm]
theorem Homotopic.symm {φ ψ : AsymptoticMorphism A B} (h : φ.Homotopic ψ) : ψ.Homotopic φ := by
  obtain ⟨H, h0, h1⟩ := h
  let rev : C(unitInterval, unitInterval) := ⟨unitInterval.symm, unitInterval.continuous_symm⟩
  exact ⟨H.postcompStarAlgHom (ContinuousMap.compNonUnitalStarAlgHom' ℂ B rev),
    by rw [← h1]; ext; simp [rev], by rw [← h0]; ext; simp [rev]⟩

/-- Closed nonunital `⋆`-subalgebra of pairs `(f, g) ∈ C(I, B) × C(I, B)` matching at `f 1 = g 0`.
-/
private def pathConcatSubalgebra (B : Type*) [NonUnitalCStarAlgebra B] :
    NonUnitalStarSubalgebra ℂ (C(unitInterval, B) × C(unitInterval, B)) where
  carrier := {p | p.1 1 = p.2 0}
  mul_mem' {_ _} hp hq := by rw [mem_ofPred_eq] at hp hq ⊢; simp [hp, hq]
  add_mem' {_ _} hp hq := by rw [mem_ofPred_eq] at hp hq ⊢; simp [hp, hq]
  zero_mem' := rfl
  smul_mem' _ {_} hp := by rw [mem_ofPred_eq] at hp ⊢; simp [hp]
  star_mem' {_} hp := by rw [mem_ofPred_eq] at hp ⊢; simp [hp]

private instance isClosed_pathConcatSubalgebra (B : Type*) [NonUnitalCStarAlgebra B] :
    IsClosed (pathConcatSubalgebra B : Set (C(unitInterval, B) × C(unitInterval, B))) :=
  isClosed_eq ((continuous_eval_const (1 : unitInterval)).comp continuous_fst)
    ((continuous_eval_const (0 : unitInterval)).comp continuous_snd)

/-- Path concatenation at `s = 1 / 2` as a nonunital `⋆`-homomorphism out of
`pathConcatSubalgebra B`. Because `pathConcatSubalgebra B` is a closed `⋆`-subalgebra of a
C⋆-algebra, it is a C⋆-algebra and this `⋆`-homomorphism is automatically continuous and
contractive. -/
private noncomputable def pathConcatStarAlgHom (B : Type*) [NonUnitalCStarAlgebra B] :
    pathConcatSubalgebra B →⋆ₙₐ[ℂ] C(unitInterval, B) where
  toFun p := ((Path.mk p.val.1 rfl rfl).trans (Path.mk p.val.2 p.property.symm rfl)).toContinuousMap
  map_smul' _ _ := by
    ext; simp only [ContinuousMap.smul_apply, ContinuousMap.toFun_eq_coe, Path.coe_toContinuousMap,
      Path.trans_apply]; split_ifs <;> rfl
  map_zero' := by
    ext; simp only [ContinuousMap.zero_apply, ContinuousMap.toFun_eq_coe, Path.coe_toContinuousMap,
      Path.trans_apply]; split_ifs <;> rfl
  map_add' _ _ := by
    ext; simp only [ContinuousMap.add_apply, ContinuousMap.toFun_eq_coe, Path.coe_toContinuousMap,
      Path.trans_apply]; split_ifs <;> rfl
  map_mul' _ _ := by
    ext; simp only [ContinuousMap.mul_apply, ContinuousMap.toFun_eq_coe, Path.coe_toContinuousMap,
      Path.trans_apply]; split_ifs <;> rfl
  map_star' _ := by
    ext; simp only [ContinuousMap.star_apply, ContinuousMap.toFun_eq_coe, Path.coe_toContinuousMap,
      Path.trans_apply]; split_ifs <;> rfl

@[trans]
theorem Homotopic.trans {φ ψ χ : AsymptoticMorphism A B}
    (h₁ : φ.Homotopic ψ) (h₂ : ψ.Homotopic χ) : φ.Homotopic χ := by
  obtain ⟨H₁, h₁0, h₁1⟩ := h₁; obtain ⟨H₂, h₂0, h₂1⟩ := h₂
  have hmatch (t a) : H₁ t a 1 = H₂ t a 0 := by
    simpa [evalAt_apply] using (AsymptoticMorphism.ext_iff.mp h₁1 t a).trans
      (AsymptoticMorphism.ext_iff.mp h₂0 t a).symm
  let P : AsymptoticMorphism A (pathConcatSubalgebra B) :=
    { toFun := fun t a ↦ ⟨(H₁ t a, H₂ t a), hmatch t a⟩
      continuous_apply' := fun a ↦
        Continuous.subtype_mk ((H₁.continuous_apply a).prodMk (H₂.continuous_apply a)) _
      map_add_tendsto' := fun a b ↦
        tendsto_subtype_rng.mpr ((H₁.map_add_tendsto a b).prodMk_nhds (H₂.map_add_tendsto a b))
      map_smul_tendsto' := fun c a ↦
        tendsto_subtype_rng.mpr ((H₁.map_smul_tendsto c a).prodMk_nhds (H₂.map_smul_tendsto c a))
      map_mul_tendsto' := fun a b ↦
        tendsto_subtype_rng.mpr ((H₁.map_mul_tendsto a b).prodMk_nhds (H₂.map_mul_tendsto a b))
      map_star_tendsto' := fun a ↦
        tendsto_subtype_rng.mpr ((H₁.map_star_tendsto a).prodMk_nhds (H₂.map_star_tendsto a)) }
  exact ⟨P.postcompStarAlgHom (pathConcatStarAlgHom B),
    by rw [← h₁0]; ext; simp [P, pathConcatStarAlgHom],
    by rw [← h₂1]; ext; simp [P, pathConcatStarAlgHom]⟩

/-- The setoid of homotopy on `AsymptoticMorphism A B`. -/
def homotopySetoid (A B : Type*) [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    Setoid (AsymptoticMorphism A B) :=
  ⟨Homotopic, ⟨Homotopic.refl, Homotopic.symm, Homotopic.trans⟩⟩

/-- Straight-line interpolation `(1 - s) • φ t a + s • ψ t a` shows that asymptotically equivalent
asymptotic morphisms are homotopic. -/
theorem Equiv.homotopic {φ ψ : AsymptoticMorphism A B} (h : φ.Equiv ψ) : φ.Homotopic ψ := by
  let φc : AsymptoticMorphism A C(unitInterval, B) :=
    φ.postcompStarAlgHom (ContinuousMap.constNonUnitalStarAlgHom ℂ unitInterval B)
  let lineHom : B →+ C(unitInterval, B) :=
    { toFun := fun b ↦ ⟨fun s ↦ (s : ℝ) • b, continuous_subtypeVal.smul continuous_const⟩
      map_zero' := by ext; simp
      map_add' := fun _ _ ↦ by ext; simp [smul_add] }
  have hline_norm (b : B) : ‖lineHom b‖ ≤ ‖b‖ :=
    (ContinuousMap.norm_le _ (norm_nonneg b)).mpr fun s ↦ by
      simp only [lineHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ContinuousMap.coe_mk, norm_smul,
        Real.norm_of_nonneg s.property.1]
      exact mul_le_of_le_one_left (norm_nonneg b) s.property.2
  have hline_cont : Continuous lineHom :=
    AddMonoidHomClass.continuous_of_bound lineHom 1
      fun b ↦ by simpa only [one_mul] using hline_norm b
  let traj (a : A) (t : Ici (1 : ℝ)) : C(unitInterval, B) := φc t a + lineHom (ψ t a - φ t a)
  have htraj_cont (a) : Continuous (traj a) :=
    (φc.continuous_apply a).add
      (hline_cont.comp ((ψ.continuous_apply a).sub (φ.continuous_apply a)))
  have htraj_diff (a) : Tendsto (fun t ↦ traj a t - φc t a) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr <| squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun t ↦ by simpa only [traj, add_sub_cancel_left] using hline_norm (ψ t a - φ t a))
      (tendsto_zero_iff_norm_tendsto_zero.mp (h.symm.tendsto a))
  have htraj_bdd (a) : ∃ C, ∀ᶠ t in atTop, ‖traj a t‖ ≤ C := by
    obtain ⟨C₀, hC₀⟩ := φc.exists_eventually_norm_le a
    refine ⟨C₀ + 1, ?_⟩
    filter_upwards [hC₀,
      (tendsto_order.mp (tendsto_zero_iff_norm_tendsto_zero.mp (htraj_diff a))).2 1 zero_lt_one]
      with t ht₀ htd
    calc ‖traj a t‖ = ‖φc t a + (traj a t - φc t a)‖ := by rw [add_sub_cancel]
      _ ≤ C₀ + 1 := (norm_add_le _ _).trans (add_le_add ht₀ htd.le)
  let sec (a : A) : Ici (1 : ℝ) →ᵇ C(unitInterval, B) :=
    BoundedContinuousFunction.ofEventuallyBoundedIci (traj a) (htraj_cont a) (htraj_bdd a)
  have hsec (a) : AsymptoticAlgebra.mk (sec a) = φc.toAsymptoticHom a := by
    rw [toAsymptoticHom_apply, AsymptoticAlgebra.mk_eq_iff]
    exact (htraj_diff a).congr fun _ ↦ by simp [sec, toBounded_apply]
  exact ⟨ofAsymptoticHomSection sec hsec,
    by ext; simp [evalAt_apply, ofAsymptoticHomSection_apply, sec, traj, φc, lineHom],
    by ext; simp [evalAt_apply, ofAsymptoticHomSection_apply, sec, traj, φc, lineHom]⟩

/-- Precomposing homotopic asymptotic morphisms with a `⋆`-homomorphism preserves homotopy. -/
theorem Homotopic.compStarAlgHom {φ ψ : AsymptoticMorphism B C} (h : φ.Homotopic ψ)
    (f : A →⋆ₙₐ[ℂ] B) : (φ.compStarAlgHom f).Homotopic (ψ.compStarAlgHom f) := by
  obtain ⟨H, h0, h1⟩ := h
  exact ⟨H.compStarAlgHom f, by rw [← h0]; ext; simp, by rw [← h1]; ext; simp⟩

/-- Postcomposing homotopic asymptotic morphisms with a `⋆`-homomorphism preserves homotopy. -/
theorem Homotopic.postcompStarAlgHom {φ ψ : AsymptoticMorphism A B} (h : φ.Homotopic ψ)
    (g : B →⋆ₙₐ[ℂ] C) : (φ.postcompStarAlgHom g).Homotopic (ψ.postcompStarAlgHom g) := by
  obtain ⟨H, h0, h1⟩ := h
  exact ⟨H.postcompStarAlgHom
    (ContinuousMap.postcompNonUnitalStarAlgHom ℂ B C g (map_continuous g)),
    by rw [← h0]; ext; simp, by rw [← h1]; ext; simp⟩

/-- **Reparameterization invariance** (Blackadar, Proposition 25.1.5): for any continuous map
`r : C(Set.Ici 1, Set.Ici 1)` with `Tendsto r atTop atTop`, `φ` is homotopic to `φ.reparam r hr`.
-/
theorem homotopic_reparam (φ : AsymptoticMorphism A B)
    (r : C(Ici (1 : ℝ), Ici (1 : ℝ))) (hr : Tendsto r atTop atTop) :
    φ.Homotopic (φ.reparam r hr) := by
  let R : C(Ici (1 : ℝ) × unitInterval, Ici (1 : ℝ)) :=
    { toFun := fun p ↦ ⟨(1 - (p.2 : ℝ)) * (p.1 : ℝ) + (p.2 : ℝ) * (r p.1 : ℝ), by
        rw [mem_Ici]
        have hp1 : (1 : ℝ) ≤ p.1 := p.1.property
        have hrp : (1 : ℝ) ≤ r p.1 := (r p.1).property
        nlinarith [p.2.property.1, sub_nonneg.mpr p.2.property.2]⟩
      continuous_toFun := by fun_prop }
  have hpull_zero {g : Ici (1 : ℝ) → B} (hg_cont : Continuous g) (hg : Tendsto g atTop (𝓝 0)) :
      Tendsto (fun t : Ici (1 : ℝ) ↦
        (⟨fun s : unitInterval ↦ g (R (t, s)),
          hg_cont.comp (R.continuous.comp (Continuous.prodMk_right t))⟩ : C(unitInterval, B)))
        atTop (𝓝 0) := by
    refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
    obtain ⟨T, hT⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hg) (ε / 2) (half_pos hε))
    obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp (hr.eventually_ge_atTop T)
    refine eventually_atTop.mpr ⟨max T T₁, fun t ht ↦ ?_⟩
    have htT : (T : ℝ) ≤ (t : ℝ) := (le_max_left T T₁).trans ht
    have hrtT : (T : ℝ) ≤ (r t : ℝ) := hT₁ t ((le_max_right T T₁).trans ht)
    rw [dist_zero_right]
    refine lt_of_le_of_lt
      ((ContinuousMap.norm_le _ (half_pos hε).le).mpr fun s ↦ ?_) (half_lt_self hε)
    have hR_ge : T ≤ R (t, s) := by
      rw [← Subtype.coe_le_coe]; simp only [R, ContinuousMap.coe_mk]
      nlinarith [s.property.1, sub_nonneg.mpr s.property.2]
    exact (dist_zero_right (g (R (t, s))) ▸ hT (R (t, s)) hR_ge).le
  let H : AsymptoticMorphism A C(unitInterval, B) :=
    { toFun := fun t a ↦
        ContinuousMap.curry ⟨fun p ↦ φ (R p) a, (φ.continuous_apply a).comp R.continuous⟩ t
      continuous_apply' := fun a ↦
        (ContinuousMap.curry
          ⟨fun p ↦ φ (R p) a, (φ.continuous_apply a).comp R.continuous⟩).continuous
      map_add_tendsto' := fun a b ↦
        (hpull_zero ((φ.continuous_apply (a + b)).sub
          ((φ.continuous_apply a).add (φ.continuous_apply b)))
          (φ.map_add_tendsto a b)).congr fun _ ↦ by ext; rfl
      map_smul_tendsto' := fun c a ↦
        (hpull_zero ((φ.continuous_apply (c • a)).sub
          (continuous_const.smul (φ.continuous_apply a)))
          (φ.map_smul_tendsto c a)).congr fun _ ↦ by ext; rfl
      map_mul_tendsto' := fun a b ↦
        (hpull_zero ((φ.continuous_apply (a * b)).sub
          ((φ.continuous_apply a).mul (φ.continuous_apply b)))
          (φ.map_mul_tendsto a b)).congr fun _ ↦ by ext; rfl
      map_star_tendsto' := fun a ↦
        (hpull_zero ((φ.continuous_apply (star a)).sub (φ.continuous_apply a).star)
          (φ.map_star_tendsto a)).congr fun _ ↦ by ext; rfl }
  refine ⟨H, ?_, ?_⟩
  · ext t a; simp only [evalAt_apply, H, ContinuousMap.curry_apply, ContinuousMap.coe_mk]
    congr 1; ext; simp [R]
  · ext t a
    simp only [evalAt_apply, reparam_apply, H, ContinuousMap.curry_apply, ContinuousMap.coe_mk]
    congr 1; ext; simp [R]

end AsymptoticMorphism

/-- The set `[[A, B]]` of homotopy classes of asymptotic morphisms between C⋆-algebras `A` and `B`.
-/
def AsymptoticHomotopy (A B : Type*) [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] : Type _ :=
  Quotient (AsymptoticMorphism.homotopySetoid A B)

namespace AsymptoticHomotopy

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The homotopy class `[[φ]] : AsymptoticHomotopy A B` of an asymptotic morphism `φ`. -/
def mk (φ : AsymptoticMorphism A B) : AsymptoticHomotopy A B :=
  Quotient.mk (AsymptoticMorphism.homotopySetoid A B) φ

instance instZero : Zero (AsymptoticHomotopy A B) := ⟨mk 0⟩

instance instInhabited : Inhabited (AsymptoticHomotopy A B) := ⟨0⟩

theorem mk_surjective : Function.Surjective (mk (A := A) (B := B)) := Quotient.mk_surjective

@[simp]
theorem mk_eq_mk_iff {φ ψ : AsymptoticMorphism A B} : mk φ = mk ψ ↔ φ.Homotopic ψ := Quotient.eq

theorem mk_eq_of_equiv {φ ψ : AsymptoticMorphism A B} (h : φ.Equiv ψ) : mk φ = mk ψ :=
  mk_eq_mk_iff.mpr h.homotopic

@[simp]
theorem mk_reparam (φ : AsymptoticMorphism A B)
    (r : C(Ici (1 : ℝ), Ici (1 : ℝ))) (hr : Tendsto r atTop atTop) :
    mk (φ.reparam r hr) = mk φ :=
  mk_eq_mk_iff.mpr (φ.homotopic_reparam r hr).symm

end AsymptoticHomotopy

end TauCeti
