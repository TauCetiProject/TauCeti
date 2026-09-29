/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.RelationModule.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Cocycle
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Frattini.Basic

/-!
# Relations from cocycles on a free pro-`p` group

A locally constant cocycle sends the kernel of a presentation to the span of its values on normal
generators. When it takes standard basis values on free generators, those values span the relation
module. Its values on Frattini elements have zero augmentation in every coordinate.
-/

public section

namespace TauCeti

open Subgroup ContCohomology Module _root_.MonoidAlgebra

universe u

attribute [local instance 2000] Ring.toAddCommGroup

variable {p : ℕ} [Fact p.Prime] {X : Type u} [Fintype X] {G : Type u} [Group G] [Finite G]
  [TopologicalSpace G] [DiscreteTopology G]

section Cocycle

variable {π : freeProP p X →ₜ* G} {D : freeProP p X → X → MonoidAlgebra (ZMod p) G}
  (hcoc : ∀ g h, D (g * h) = single (π g) (1 : ZMod p) • D h + D g)
include hcoc

omit [Fintype X] [Finite G] [DiscreteTopology G] in
private theorem map_one_of_cocycle : D 1 = 0 := by
  have h := hcoc 1 1
  rw [mul_one, map_one, ← one_def, one_smul] at h
  simpa using h

omit [Fintype X] [Finite G] [DiscreteTopology G] in
/-- On the kernel of `π` the cocycle is additive. -/
private theorem map_mul_of_cocycle {ρ : freeProP p X} (hρ : π ρ = 1) (σ : freeProP p X) :
    D (ρ * σ) = D σ + D ρ := by
  rw [hcoc, hρ, ← one_def, one_smul]

omit [Fintype X] [Finite G] [DiscreteTopology G] in
/-- On the kernel of `π` the cocycle is equivariant for conjugation. -/
private theorem map_conj_of_cocycle (v : freeProP p X) {ρ : freeProP p X} (hρ : π ρ = 1) :
    D (v * ρ * v⁻¹) = single (π v) (1 : ZMod p) • D ρ := by
  have h := hcoc v v⁻¹
  rw [mul_inv_cancel, map_one_of_cocycle hcoc] at h
  rw [hcoc, hcoc v ρ, map_mul, hρ, mul_one, add_left_comm, ← h, add_zero]

omit [Fintype X] [Finite G] in
/-- **The cocycle maps the kernel of `π` into the span of the images of its normal generators.** If
the kernel of `π` is the closed normal closure of a finite set `s`, then `D w` is an
`𝔽_p[G]`-combination of the `D ρ`, `ρ ∈ s`, for every `w` with `π w = 1`: the set of such `w` is
closed and contains the normal closure of `s`, since `D` is additive and conjugation-equivariant
on the kernel. -/
theorem mem_span_of_map_eq_one {s : Finset (freeProP p X)}
    (hs : ∀ w, π w = 1 ↔ w ∈ (normalClosure (s : Set (freeProP p X))).topologicalClosure)
    (hD : IsLocallyConstant D) {w : freeProP p X} (hw : π w = 1) :
    D w ∈ Submodule.span (MonoidAlgebra (ZMod p) G) (Set.range fun ρ : s ↦ D ρ) := by
  set S := Submodule.span (MonoidAlgebra (ZMod p) G) (Set.range fun ρ : s ↦ D ρ)
  have hS : IsClosed (D ⁻¹' (S : Set (X → MonoidAlgebra (ZMod p) G))) := by
    rw [← isOpen_compl_iff, ← Set.preimage_compl]
    exact hD _
  have hC : IsClosed {w | π w = 1 ∧ D w ∈ S} :=
    (isClosed_eq π.continuous continuous_const).inter hS
  have hsub : (normalClosure (s : Set (freeProP p X)) : Set (freeProP p X)) ⊆
      {w | π w = 1 ∧ D w ∈ S} := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨ρ, hρs, c, rfl⟩ := Group.mem_conjugatesOfSet_iff.1 hw |>.imp fun _ h ↦
        h.imp_right isConj_iff.1
      have hρ : π ρ = 1 := (hs ρ).2 (le_topologicalClosure _ (subset_normalClosure hρs))
      refine ⟨by simp [hρ], ?_⟩
      rw [map_conj_of_cocycle hcoc c hρ]
      exact S.smul_mem _ (Submodule.subset_span ⟨⟨ρ, hρs⟩, rfl⟩)
    | one => exact ⟨map_one π, map_one_of_cocycle hcoc ▸ zero_mem S⟩
    | mul v w _ _ hv hw =>
      refine ⟨by rw [map_mul, hv.1, hw.1, one_mul], ?_⟩
      rw [map_mul_of_cocycle hcoc hv.1]
      exact add_mem hw.2 hv.2
    | inv v _ hv =>
      refine ⟨by rw [map_inv, hv.1, inv_one], ?_⟩
      have h := map_mul_of_cocycle hcoc hv.1 v⁻¹
      rw [mul_inv_cancel, map_one_of_cocycle hcoc] at h
      rw [eq_neg_of_add_eq_zero_left h.symm]
      exact neg_mem hv.2
  have hw' : w ∈ _root_.closure (normalClosure (s : Set (freeProP p X)) : Set _) := by
    rw [← topologicalClosure_coe]
    exact (hs w).1 hw
  exact (closure_minimal hsub hC hw').2

omit [Finite G] in
/-- **The relations among the `π xᵢ - 1` are spanned by the images of the relators.** Let
`π : F ↠ G` be a continuous surjection from a free pro-`p` group onto a discrete group, whose
kernel is the closed normal closure of a finite set `s`, and let `D : F → 𝔽_p[G]^X` be a locally
constant cocycle with `D xᵢ = eᵢ`. Then the relation module of the family `π xᵢ` is spanned over
`𝔽_p[G]` by the `D ρ`, `ρ ∈ s`. -/
theorem relationModule_le_span [DecidableEq X] (hπ : Function.Surjective π)
    {s : Finset (freeProP p X)}
    (hs : ∀ w, π w = 1 ↔ w ∈ (normalClosure (s : Set (freeProP p X))).topologicalClosure)
    (hD : IsLocallyConstant D) (hDof : ∀ i, D (freeProP.of i) = Pi.single i 1) :
    MonoidAlgebra.relationModule (ZMod p) G (fun i ↦ π (freeProP.of i)) ≤
      Submodule.span (MonoidAlgebra (ZMod p) G) (Set.range fun ρ : s ↦ D ρ) := by
  classical
  set S := Submodule.span (MonoidAlgebra (ZMod p) G) (Set.range fun ρ : s ↦ D ρ)
  -- Modulo `S`, the cocycle descends to a function `δ` on `G`.
  set S' := S.restrictScalars (ZMod p)
  let δ : G → (X → MonoidAlgebra (ZMod p) G) ⧸ S' := fun g ↦ S'.mkQ (D (Function.surjInv hπ g))
  have hδ (v : freeProP p X) : δ (π v) = S'.mkQ (D v) := by
    set u := Function.surjInv hπ (π v)
    have hu : π u = π v := Function.surjInv_eq hπ _
    have hρ : π (u⁻¹ * v) = 1 := by rw [map_mul, map_inv, hu, inv_mul_cancel]
    have hv : D v = single (π u) (1 : ZMod p) • D (u⁻¹ * v) + D u := by
      rw [← hcoc, mul_inv_cancel_left]
    rw [hv, map_add, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero S').2
      ((Submodule.restrictScalars_mem _ _ _).2
        (S.smul_mem _ (mem_span_of_map_eq_one hcoc hs hD hρ))), zero_add]
  -- Extending `δ` linearly to `𝔽_p[G]` inverts the map `a ↦ ∑ aᵢ (π xᵢ - 1)` modulo `S`.
  let Ψ : MonoidAlgebra (ZMod p) G →ₗ[ZMod p] (X → MonoidAlgebra (ZMod p) G) ⧸ S' :=
    (MonoidAlgebra.basis G (ZMod p)).constr (ZMod p) δ
  have hΨ (g : G) : Ψ (single g 1) = δ g := by
    rw [← MonoidAlgebra.basis_apply, Basis.constr_basis]
  have hcomp : Ψ ∘ₗ (Fintype.linearCombination (MonoidAlgebra (ZMod p) G)
      fun i ↦ single (π (freeProP.of i)) (1 : ZMod p) - 1).restrictScalars (ZMod p) =
      S'.mkQ := by
    refine LinearMap.pi_ext' fun i ↦ (MonoidAlgebra.basis G (ZMod p)).ext fun h ↦ ?_
    obtain ⟨v, rfl⟩ := hπ h
    have hsingle : single (π v) (1 : ZMod p) • (Pi.single i 1 : X → MonoidAlgebra (ZMod p) G) =
        Pi.single i (single (π v) (1 : ZMod p)) := by
      rw [← Pi.single_smul', smul_eq_mul, mul_one]
    simp only [LinearMap.comp_apply, LinearMap.coe_single, LinearMap.restrictScalars_apply,
      Fintype.linearCombination_apply_single, MonoidAlgebra.basis_apply, smul_eq_mul, mul_sub,
      mul_one, single_mul_single, map_sub, hΨ, ← map_mul, hδ, hcoc, hDof, hsingle, map_add,
      add_sub_cancel_right]
  intro a ha
  have h := LinearMap.congr_fun hcomp a
  rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Fintype.linearCombination_apply] at h
  simp only [smul_eq_mul, MonoidAlgebra.mem_relationModule_iff.1 ha, map_zero] at h
  exact (Submodule.restrictScalars_mem _ _ _).1 ((Submodule.Quotient.mk_eq_zero S').1 h.symm)

omit [Fintype X] [Finite G] [DiscreteTopology G] in
/-- **The cocycle image of a Frattini element has every coordinate in the augmentation ideal.**
The cocycle, composed with the augmentation
`𝔽_p[G] → 𝔽_p`, is a continuous homomorphism to an elementary abelian `p`-group, so it vanishes
on the Frattini subgroup. -/
theorem augmentation_apply_eq_zero_of_mem_proPFrattini (hD : IsLocallyConstant D)
    {ρ : freeProP p X} (hρ : ρ ∈ proPFrattini p (freeProP p X)) (i : X) :
    MonoidAlgebra.augmentation (ZMod p) G (D ρ i) = 0 := by
  set ε := MonoidAlgebra.augmentation (ZMod p) G
  let χ : freeProP p X →* Multiplicative (X → ZMod p) :=
    { toFun w := Multiplicative.ofAdd fun i ↦ ε (D w i)
      map_one' := ofAdd_eq_one.2 (funext fun i ↦ by simp [map_one_of_cocycle hcoc])
      map_mul' g h := by
        rw [← ofAdd_add]
        congr 1
        ext i
        simp [hcoc, ε, add_comm] }
  have hclosed : IsClosed (χ.ker : Set (freeProP p X)) :=
    (hD.comp fun m : X → MonoidAlgebra (ZMod p) G ↦
      Multiplicative.ofAdd fun i ↦ ε (m i)).isClosed_fiber 1
  have hexp : Monoid.exponent (Multiplicative (X → ZMod p)) ∣ p :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x ↦ by
      rw [← ofAdd_toAdd x, ← ofAdd_nsmul, ofAdd_eq_one]
      ext i
      simp
  have h := MonoidHom.mem_ker.1 (proPFrattini_le_ker_of_exponent_dvd Fact.out χ hclosed hexp hρ)
  exact congrFun (ofAdd_eq_one.1 h) i

end Cocycle

end TauCeti
