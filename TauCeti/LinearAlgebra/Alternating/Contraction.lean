/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Alternating.Conormal
public import TauCeti.LinearAlgebra.Alternating.Curry
public import TauCeti.LinearAlgebra.Alternating.TopDegree

/-!
# Contraction of conormal orientations

Contracting a top-degree conormal form by a vector outside the tangent subspace
produces a nonzero conormal form for the enlarged tangent subspace. This is the
orientation operation for a transverse polyhedral sweep.

The construction uses Mathlib's `AlternatingMap.curryLeft`, the top-degree vanishing criterion
`AlternatingMap.eq_zero_of_curryLeft_eq_zero`, and descent through
`Submodule.conormalFormsEquiv` to the normal quotient.

## Attribution

Adapted from `Mei/LinearAlgebra/Alternating/Contraction.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`9cf969cdee9748087aae45dbf4888a130890655c` (Apache 2.0).
Original author: Codex; original copyright: Mei contributors.
-/

public section

open Module

namespace Submodule

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {k : ℕ}

/-- Contraction of a conormal form annihilates both the old subspace and the
contracting vector. -/
theorem curryLeft_mem_conormalForms {W : Submodule R M}
    {α : M [⋀^Fin (k + 1)]→ₗ[R] R} (hα : α ∈ W.conormalForms (Fin (k + 1))) (n : M) :
    α.curryLeft n ∈ (W ⊔ R ∙ n).conormalForms (Fin k) := by
  rw [Submodule.mem_conormalForms] at hα ⊢
  intro v j hv
  obtain ⟨w, hw, z, hz, he⟩ := Submodule.mem_sup.mp hv
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hz
  rw [← Function.update_eq_self j v, ← he, AlternatingMap.map_update_add,
    AlternatingMap.map_update_smul]
  have hw0 : α.curryLeft n (Function.update v j w) = 0 :=
    hα _ j.succ (by simpa using hw)
  have hn0 : α.curryLeft n (Function.update v j n) = 0 :=
    α.map_eq_zero_of_eq _ (by simp) (Fin.succ_ne_zero j).symm
  simp [hw0, hn0]

end CommRing

variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M] {k : ℕ}

/-- In top conormal degree, contraction vanishes exactly in tangent directions. -/
theorem conormalForms_curryLeft_eq_zero_iff
    {W : Submodule R M} (hk : finrank R (M ⧸ W) = k + 1)
    {α : M [⋀^Fin (k + 1)]→ₗ[R] R} (hα : α ∈ W.conormalForms (Fin (k + 1)))
    (hα0 : α ≠ 0) (n : M) : α.curryLeft n = 0 ↔ n ∈ W := by
  have : FiniteDimensional R (M ⧸ W) := FiniteDimensional.of_finrank_pos (by omega)
  let β := W.conormalFormsEquiv.symm ⟨α, hα⟩
  have hβ : β.compLinearMap W.mkQ = α := by
    ext v
    simpa only [AlternatingMap.compLinearMap_apply, Submodule.mkQ_apply] using
      W.conormalFormsEquiv_symm_apply_mk ⟨α, hα⟩ v
  have hβ0 : β ≠ 0 := by
    intro hz
    exact hα0 (by rw [← hβ, hz, AlternatingMap.zero_compLinearMap])
  have hi := AlternatingMap.compLinearMap_inj W.mkQ W.mkQ_surjective (β.curryLeft (W.mkQ n)) 0
  rw [AlternatingMap.zero_compLinearMap] at hi
  rw [← hβ, AlternatingMap.curryLeft_compLinearMap, hi]
  constructor
  · intro hz
    by_contra hn
    have hn0 : W.mkQ n ≠ 0 := by
      rw [Submodule.mkQ_apply, ne_eq, Submodule.Quotient.mk_eq_zero]
      exact hn
    exact hβ0 (AlternatingMap.eq_zero_of_curryLeft_eq_zero hk β hn0 hz)
  · intro hn
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr hn, map_zero]

/-- A transverse contraction of a nonzero top-degree conormal form is nonzero. -/
theorem curryLeft_ne_zero_of_notMem
    {W : Submodule R M} (hk : finrank R (M ⧸ W) = k + 1)
    {α : M [⋀^Fin (k + 1)]→ₗ[R] R} (hα : α ∈ W.conormalForms (Fin (k + 1)))
    (hα0 : α ≠ 0) {n : M} (hn : n ∉ W) : α.curryLeft n ≠ 0 :=
  (conormalForms_curryLeft_eq_zero_iff hk hα hα0 n).not.mpr hn

/-- Contraction by a transverse vector determines a top-degree conormal form. -/
theorem conormalForms_curryLeft_inj
    {W : Submodule R M} (hk : finrank R (M ⧸ W) = k + 1)
    {α β : M [⋀^Fin (k + 1)]→ₗ[R] R}
    (hα : α ∈ W.conormalForms (Fin (k + 1)))
    (hβ : β ∈ W.conormalForms (Fin (k + 1))) {n : M} (hn : n ∉ W) :
    α.curryLeft n = β.curryLeft n ↔ α = β := by
  constructor
  · intro he
    by_contra hne
    have hz : (α - β).curryLeft n = 0 := by
      ext v
      simpa only [AlternatingMap.curryLeft_apply_apply, sub_apply,
        zero_apply] using
        sub_eq_zero.mpr (AlternatingMap.congr_fun he v)
    exact hn ((conormalForms_curryLeft_eq_zero_iff hk (sub_mem hα hβ)
      (sub_ne_zero.mpr hne) n).mp hz)
  · rintro rfl
    rfl

end Submodule

namespace Module.Ray

variable {R M : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] {k : ℕ}
  {W : Submodule R M}

/-- Contract a top conormal orientation by a transverse vector, placing that
vector first in the representing alternating form. -/
noncomputable def contract (o : Module.Ray R (M [⋀^Fin (k + 1)]→ₗ[R] R))
    (ho : o.IsConormal W) (hk : finrank R (M ⧸ W) = k + 1)
    (n : M) (hn : n ∉ W) : Module.Ray R (M [⋀^Fin k]→ₗ[R] R) :=
  rayOfNeZero R (o.someVector.curryLeft n) <| by
    apply Submodule.curryLeft_ne_zero_of_notMem hk _ o.someVector_ne_zero hn
    rwa [← o.someVector_ray, isConormal_rayOfNeZero_iff] at ho

/-- Contraction can be computed using any nonzero representing form. -/
@[simp]
theorem contract_rayOfNeZero {α : M [⋀^Fin (k + 1)]→ₗ[R] R} (hα : α ≠ 0)
    (ho : (rayOfNeZero R α hα).IsConormal W) (hk : finrank R (M ⧸ W) = k + 1)
    (n : M) (hn : n ∉ W) :
    (rayOfNeZero R α hα).contract ho hk n hn =
      rayOfNeZero R (α.curryLeft n)
        (Submodule.curryLeft_ne_zero_of_notMem hk
          ((isConormal_rayOfNeZero_iff hα).mp ho) hα hn) := by
  apply (ray_eq_iff _ _).mpr
  exact ((ray_eq_iff (Module.Ray.someVector_ne_zero _) hα).mp
    (Module.Ray.someVector_ray _)).map
      ((LinearMap.applyₗ n).comp AlternatingMap.curryLeftLinearMap)

/-- The contracted orientation has the sign of the original orientation with the
contracting vector placed first. -/
@[simp]
theorem evalSign_contract (o : Module.Ray R (M [⋀^Fin (k + 1)]→ₗ[R] R))
    (ho : o.IsConormal W) (hk : finrank R (M ⧸ W) = k + 1) (n : M) (hn : n ∉ W)
    (v : Fin k → M) :
    (o.contract ho hk n hn).evalSign v = o.evalSign (Matrix.vecCons n v) := by
  induction o using Module.Ray.ind with
  | h α hα =>
    rw [contract_rayOfNeZero, evalSign_rayOfNeZero, evalSign_rayOfNeZero,
      AlternatingMap.curryLeft_apply_apply]

/-- The contracted orientation is conormal to the old tangent space enlarged by
the sweeping line. -/
theorem isConormal_contract (o : Module.Ray R (M [⋀^Fin (k + 1)]→ₗ[R] R))
    (ho : o.IsConormal W) (hk : finrank R (M ⧸ W) = k + 1) (n : M) (hn : n ∉ W) :
    (o.contract ho hk n hn).IsConormal (W ⊔ R ∙ n) := by
  induction o using Module.Ray.ind with
  | h α hα =>
    rw [contract_rayOfNeZero, isConormal_rayOfNeZero_iff]
    exact Submodule.curryLeft_mem_conormalForms ((isConormal_rayOfNeZero_iff hα).mp ho) n

/-- Contraction commutes with reversal of the orientation. -/
@[simp]
theorem contract_neg (o : Module.Ray R (M [⋀^Fin (k + 1)]→ₗ[R] R))
    (ho : o.IsConormal W) (hk : finrank R (M ⧸ W) = k + 1) (n : M) (hn : n ∉ W) :
    (-o).contract (isConormal_neg_iff.mpr ho) hk n hn = -o.contract ho hk n hn := by
  induction o using Module.Ray.ind with
  | h α hα =>
    simp only [neg_rayOfNeZero, contract_rayOfNeZero]
    congr 1

/-- Contracting two top-degree conormal orientations by the same transverse
vector preserves and reflects equality. -/
@[simp]
theorem contract_eq_contract_iff
    (o p : Module.Ray R (M [⋀^Fin (k + 1)]→ₗ[R] R))
    (ho : o.IsConormal W) (hp : p.IsConormal W)
    (hk : finrank R (M ⧸ W) = k + 1) (n : M) (hn : n ∉ W) :
    o.contract ho hk n hn = p.contract hp hk n hn ↔ o = p := by
  induction o using Module.Ray.ind with
  | h α hα =>
    induction p using Module.Ray.ind with
    | h β hβ =>
      rw [contract_rayOfNeZero, contract_rayOfNeZero, ray_eq_iff, ray_eq_iff]
      constructor
      · intro he
        obtain ⟨c, hc, he⟩ := he.exists_pos_left
          (Submodule.curryLeft_ne_zero_of_notMem hk
            ((isConormal_rayOfNeZero_iff hα).mp ho) hα hn)
          (Submodule.curryLeft_ne_zero_of_notMem hk
            ((isConormal_rayOfNeZero_iff hβ).mp hp) hβ hn)
        have hab : c • α = β := (Submodule.conormalForms_curryLeft_inj hk
          (Submodule.smul_mem _ c ((isConormal_rayOfNeZero_iff hα).mp ho))
          ((isConormal_rayOfNeZero_iff hβ).mp hp) hn).mp (by simpa using he)
        rw [← hab]
        exact SameRay.sameRay_pos_smul_right α hc
      · rintro he
        exact he.map ((LinearMap.applyₗ n).comp AlternatingMap.curryLeftLinearMap)

/-- Contraction depends only on the orientation and vector, independently of the
subspace used to certify conormality and transversality. -/
theorem contract_congr (o p : Module.Ray R (M [⋀^Fin (k + 1)]→ₗ[R] R))
    {U : Submodule R M} (ho : o.IsConormal W) (hp : p.IsConormal U)
    (hk : finrank R (M ⧸ W) = k + 1) (hl : finrank R (M ⧸ U) = k + 1)
    (n : M) (hn : n ∉ W) (hm : n ∉ U) (hop : o = p) :
    o.contract ho hk n hn = p.contract hp hl n hm := by
  subst p
  rfl

/-- Successive transverse contractions anticommute. The dimension and transversality
proofs simply ensure that both successive contractions are defined. -/
theorem contract_contract_eq_neg (o : Module.Ray R (M [⋀^Fin (k + 2)]→ₗ[R] R))
    (ho : o.IsConormal W) (hk : finrank R (M ⧸ W) = k + 2)
    (n m : M) (hn : n ∉ W) (hm : m ∉ W)
    (hkn : finrank R (M ⧸ (W ⊔ R ∙ n)) = k + 1)
    (hkm : finrank R (M ⧸ (W ⊔ R ∙ m)) = k + 1)
    (hmn : m ∉ W ⊔ R ∙ n) (hnm : n ∉ W ⊔ R ∙ m) :
    (o.contract ho hk n hn).contract (o.isConormal_contract ho hk n hn) hkn m hmn =
      -((o.contract ho hk m hm).contract (o.isConormal_contract ho hk m hm) hkm n hnm) := by
  induction o using Module.Ray.ind with
  | h α hα =>
    simp only [contract_rayOfNeZero, neg_rayOfNeZero]
    congr 1
    exact AlternatingMap.curryLeft_curryLeft_eq_neg α n m

end Module.Ray
