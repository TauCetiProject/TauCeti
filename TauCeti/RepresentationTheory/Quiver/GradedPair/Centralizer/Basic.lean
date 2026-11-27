/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import TauCeti.RepresentationTheory.Quiver.GradedPair.Image
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Projection
import TauCeti.Algebra.DirectSum.Internal

/-!
# Opposite-degree centralizers of raising and lowering pairs

For a raising or lowering pair `P = (V, T)` of step direction `d`, the opposite-degree centralizer
`TauCeti.GradedPair.centralizer P` is the complex submodule of endomorphisms `L` of `V` which are
homogeneous of degree `-d.step` and satisfy `L ∘ₗ T = T ∘ₗ L`. Each `L ∈ P.centralizer`
therefore defines a graded pair `P.oppositePair L` on the same grading in the reverse direction
`d.reverse`.

Because `L` commutes with `T`, it leaves `LinearMap.range (T ^ k)` (and in particular
`LinearMap.range T`) stable. On any model `M : P.SubmoduleModel W` of a centralizer-stable
submodule, restriction gives a complex linear map `M.restrictCentralizer`; specializing to the
chosen image model `P.imageModel` gives
`P.restrictCentralizer : P.centralizer →ₗ[ℂ] P.imageModel.pair.centralizer`.

The main theorem `TauCeti.GradedPair.centralizer_image_extension` shows that any endomorphism `L'`
of `LinearMap.range P.operator` that shifts the induced grading by `-d.step` and commutes with
the restricted operator extends to an element of `P.centralizer`. Consequently,
`P.restrictCentralizer` is surjective for both raising and lowering pairs
(`TauCeti.GradedPair.restrictCentralizer_surjective`).

## Main definitions

* `TauCeti.GradedPair.centralizer P`: opposite-degree endomorphisms commuting with `P.operator`.
* `TauCeti.GradedPair.oppositePair P L`: the opposite-direction graded pair attached to `L`.
* `TauCeti.GradedPairEquiv.centralizerEquiv e`: conjugation equivalence of centralizers along a
  graded equivalence of pairs.
* `TauCeti.GradedPair.centralizerShiftEquiv P c`: identification of centralizers under shifting.
* `TauCeti.GradedPair.SubmoduleModel.restrictCentralizer`: restriction of centralizer elements to
  a centralizer-stable submodule model.
* `TauCeti.GradedPair.restrictCentralizer P`: restriction to the chosen image model of `P`.

## Main results

* `TauCeti.GradedPair.SubmoduleModel.restrictCentralizer_comp_centralizerEquiv`: conjugation
  commutes with restriction through the induced image equivalence.
* `TauCeti.GradedPair.centralizer_image_extension`: every opposite-degree commuting endomorphism
  on `LinearMap.range P.operator` extends to `P.centralizer`.
* `TauCeti.GradedPair.restrictCentralizer_surjective`: centralizer restriction to the actual
  image is surjective in both step directions.

## References

* H. Atobe, S. Kondo, S. Yasuda, *Local newforms for the general linear groups over a
  non-archimedean local field*, Forum of Mathematics, Pi 10 (2022), e24, §3.1 and Lemma 3.2.
* C. Mœglin, J.-L. Waldspurger, *Sur l'involution de Zelevinski*, J. reine angew. Math. 372
  (1986), 136–177, §II.1 and Lemma II.4.
-/

public section

open Module

namespace TauCeti

namespace GradedPair

variable {S T : GradedCoordSpace} {d : StepDirection}

/-! ### Opposite-degree centralizer and opposite pairs -/

/-- The opposite-degree centralizer of a pair `P`: the complex submodule of endomorphisms that
are homogeneous of degree `-d.step` and commute with `P.operator`. -/
def centralizer (P : GradedPair S d) : Submodule ℂ (Module.End ℂ S.Carrier) :=
  LinearMap.homogeneousSubmodule S.grade S.grade (-d.step) ⊓
    (Subalgebra.centralizer ℂ {P.operator}).toSubmodule

@[simp]
theorem mem_centralizer_iff {P : GradedPair S d} {L : Module.End ℂ S.Carrier} :
    L ∈ P.centralizer ↔
      LinearMap.IsHomogeneous L S.grade S.grade (-d.step) ∧
        L ∘ₗ P.operator = P.operator ∘ₗ L := by
  simp only [centralizer, Submodule.mem_inf, LinearMap.mem_homogeneousSubmodule,
    Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff,
    forall_eq, Module.End.mul_eq_comp, eq_comm]

/-- A member of `P.centralizer` is homogeneous of degree `-d.step`. -/
theorem centralizer_isHomogeneous {P : GradedPair S d} (L : P.centralizer) :
    LinearMap.IsHomogeneous (L : Module.End ℂ S.Carrier) S.grade S.grade (-d.step) :=
  (mem_centralizer_iff.1 L.property).1

/-- A member of `P.centralizer` commutes with `P.operator`. -/
theorem centralizer_comp_operator {P : GradedPair S d} (L : P.centralizer) :
    (L : Module.End ℂ S.Carrier) ∘ₗ P.operator =
      P.operator ∘ₗ (L : Module.End ℂ S.Carrier) :=
  (mem_centralizer_iff.1 L.property).2

@[simp]
theorem centralizer_operator_apply {P : GradedPair S d} (L : P.centralizer) (v : S.Carrier) :
    (L : Module.End ℂ S.Carrier) (P.operator v) =
      P.operator ((L : Module.End ℂ S.Carrier) v) :=
  congrFun (congrArg DFunLike.coe (centralizer_comp_operator L)) v

/-- The opposite-degree centralizer of the zero pair consists of all endomorphisms homogeneous of
degree `-d.step`. -/
@[simp]
theorem centralizer_zero (S : GradedCoordSpace) (d : StepDirection) :
    (0 : GradedPair S d).centralizer =
      LinearMap.homogeneousSubmodule S.grade S.grade (-d.step) := by
  ext L
  simp

/-- The opposite-direction graded pair on `S` associated to `L ∈ P.centralizer`. -/
def oppositePair (P : GradedPair S d) (L : P.centralizer) : GradedPair S d.reverse where
  operator := L
  isHomogeneous := by
    simpa only [StepDirection.step_reverse] using centralizer_isHomogeneous L

@[simp]
theorem oppositePair_operator (P : GradedPair S d) (L : P.centralizer) :
    (P.oppositePair L).operator = L :=
  (rfl)

@[simp]
theorem oppositePair_zero (P : GradedPair S d) : P.oppositePair 0 = 0 :=
  (rfl)

/-- The operator of `P` belongs to the centralizer of `P.oppositePair L`. -/
theorem operator_mem_centralizer_oppositePair (P : GradedPair S d) (L : P.centralizer) :
    P.operator ∈ (P.oppositePair L).centralizer := by
  rw [mem_centralizer_iff, oppositePair_operator, StepDirection.step_reverse, neg_neg]
  exact ⟨P.isHomogeneous, (centralizer_comp_operator L).symm⟩

/-- Shifting a pair preserves its opposite-degree centralizer as a submodule of endomorphisms. -/
@[simp]
theorem centralizer_shift (P : GradedPair S d) (c : ℤ) :
    (P.shift c).centralizer = P.centralizer := by
  ext L
  simp only [mem_centralizer_iff, GradedCoordSpace.grade_shift, operator_shift]
  exact and_congr LinearMap.isHomogeneous_shift_iff Iff.rfl

/-- Shifting a pair gives a canonical linear equivalence between its centralizers, induced by
the identity on endomorphisms. -/
def centralizerShiftEquiv (P : GradedPair S d) (c : ℤ) :
    P.centralizer ≃ₗ[ℂ] (P.shift c).centralizer :=
  LinearEquiv.ofEq _ _ (P.centralizer_shift c).symm

@[simp]
theorem coe_centralizerShiftEquiv_apply (P : GradedPair S d) (c : ℤ) (L : P.centralizer) :
    ((P.centralizerShiftEquiv c L : (P.shift c).centralizer) : Module.End ℂ S.Carrier) = L :=
  (rfl)

@[simp]
theorem coe_centralizerShiftEquiv_symm_apply (P : GradedPair S d) (c : ℤ)
    (L : (P.shift c).centralizer) :
    (((P.centralizerShiftEquiv c).symm L : P.centralizer) : Module.End ℂ S.Carrier) = L :=
  (rfl)

end GradedPair

/-! ### Conjugation by a graded equivalence -/

namespace GradedPairEquiv

variable {S T U : GradedCoordSpace} {d : StepDirection}
  {P : GradedPair S d} {Q : GradedPair T d} {R : GradedPair U d}

/-- Conjugation by a graded equivalence maps `P.centralizer` onto `Q.centralizer`. -/
theorem map_centralizer (e : GradedPairEquiv P Q) :
    P.centralizer.map (e.toLinearEquiv.conj : Module.End ℂ S.Carrier →ₗ[ℂ] Module.End ℂ T.Carrier) =
      Q.centralizer := by
  ext L
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨K, hK, rfl⟩
    obtain ⟨hKhom, hKcomm⟩ := GradedPair.mem_centralizer_iff.1 hK
    have hconj (x : T.Carrier) :
        ((e.toLinearEquiv.conj : Module.End ℂ S.Carrier →ₗ[ℂ] Module.End ℂ T.Carrier) K) x =
          e (K (e.symm x)) := by
      rw [LinearEquiv.coe_coe, LinearEquiv.conj_apply_apply, coe_toLinearEquiv,
        ← toLinearEquiv_symm, coe_toLinearEquiv]
    have hcomm' (y : S.Carrier) : K (P.operator y) = P.operator (K y) :=
      congrFun (congrArg DFunLike.coe hKcomm) y
    refine GradedPair.mem_centralizer_iff.2 ⟨LinearMap.isHomogeneous_def.2 fun a v hv ↦ ?_,
      LinearMap.ext fun v ↦ ?_⟩
    · rw [hconj, e.mem_grade_iff]
      exact hKhom.map_mem (e.symm.mem_grade_iff.2 hv)
    · simp only [LinearMap.comp_apply, hconj]
      rw [e.symm.map_operator, hcomm', e.map_operator]
  · intro hL
    obtain ⟨hLhom, hLcomm⟩ := GradedPair.mem_centralizer_iff.1 hL
    have hconj (x : S.Carrier) : (e.toLinearEquiv.symm.conj L) x = e.symm (L (e x)) := by
      rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm, coe_toLinearEquiv,
        ← toLinearEquiv_symm, coe_toLinearEquiv]
    have hcomm' (y : T.Carrier) : L (Q.operator y) = Q.operator (L y) :=
      congrFun (congrArg DFunLike.coe hLcomm) y
    refine ⟨e.toLinearEquiv.symm.conj L, GradedPair.mem_centralizer_iff.2
      ⟨LinearMap.isHomogeneous_def.2 fun a v hv ↦ ?_, LinearMap.ext fun v ↦ ?_⟩, ?_⟩
    · rw [hconj, e.symm.mem_grade_iff]
      exact hLhom.map_mem (e.mem_grade_iff.2 hv)
    · simp only [LinearMap.comp_apply, hconj]
      rw [e.map_operator, hcomm', ← e.symm.map_operator]
    · simp

/-- Conjugation by a graded equivalence gives a complex linear equivalence between opposite-degree
centralizers. -/
def centralizerEquiv (e : GradedPairEquiv P Q) : P.centralizer ≃ₗ[ℂ] Q.centralizer :=
  (e.toLinearEquiv.conj.submoduleMap P.centralizer).trans
    (LinearEquiv.ofEq _ _ e.map_centralizer)

@[simp]
theorem coe_centralizerEquiv_apply (e : GradedPairEquiv P Q) (L : P.centralizer) :
    (e.centralizerEquiv L : Module.End ℂ T.Carrier) =
      e.toLinearEquiv.conj (L : Module.End ℂ S.Carrier) :=
  (rfl)

/-- Conjugation by `e` intertwines `e` with `e.centralizerEquiv`. -/
theorem centralizerEquiv_apply_apply (e : GradedPairEquiv P Q) (L : P.centralizer)
    (v : S.Carrier) :
    (e.centralizerEquiv L : Module.End ℂ T.Carrier) (e v) =
      e ((L : Module.End ℂ S.Carrier) v) := by
  rw [coe_centralizerEquiv_apply, LinearEquiv.conj_apply_apply, coe_toLinearEquiv,
    ← toLinearEquiv_symm, coe_toLinearEquiv, e.symm_apply_apply]

@[simp]
theorem centralizerEquiv_symm (e : GradedPairEquiv P Q) :
    e.centralizerEquiv.symm = e.symm.centralizerEquiv := by
  refine LinearEquiv.ext fun L ↦ Subtype.ext (LinearMap.ext fun w ↦ e.toLinearEquiv.injective ?_)
  calc
    e ((e.centralizerEquiv.symm L : Module.End ℂ S.Carrier) w)
      = (e.centralizerEquiv (e.centralizerEquiv.symm L) : Module.End ℂ T.Carrier) (e w) :=
        (e.centralizerEquiv_apply_apply _ w).symm
    _ = (L : Module.End ℂ T.Carrier) (e w) := by simp
    _ = e (e.symm ((L : Module.End ℂ T.Carrier) (e w))) := (e.apply_symm_apply _).symm
    _ = e ((e.symm.centralizerEquiv L : Module.End ℂ S.Carrier) (e.symm (e w))) := by
        rw [e.symm.centralizerEquiv_apply_apply]
    _ = e ((e.symm.centralizerEquiv L : Module.End ℂ S.Carrier) w) := by rw [e.symm_apply_apply]

@[simp]
theorem centralizerEquiv_refl (P : GradedPair S d) :
    (refl P).centralizerEquiv = LinearEquiv.refl ℂ P.centralizer := by
  refine LinearEquiv.ext fun L ↦ Subtype.ext (LinearMap.ext fun v ↦ ?_)
  rw [coe_centralizerEquiv_apply, LinearEquiv.conj_apply_apply, coe_toLinearEquiv,
    ← toLinearEquiv_symm, coe_toLinearEquiv]
  rw [← refl_apply ((refl P).symm v), apply_symm_apply, refl_apply]
  rfl

theorem centralizerEquiv_trans (e : GradedPairEquiv P Q) (f : GradedPairEquiv Q R) :
    (e.trans f).centralizerEquiv = e.centralizerEquiv.trans f.centralizerEquiv := by
  refine LinearEquiv.ext fun L ↦ Subtype.ext (LinearMap.ext fun v ↦ ?_)
  obtain ⟨u, rfl⟩ := (e.trans f).toLinearEquiv.surjective v
  rw [coe_toLinearEquiv, centralizerEquiv_apply_apply, trans_apply, trans_apply,
    LinearEquiv.trans_apply, centralizerEquiv_apply_apply, centralizerEquiv_apply_apply]

/-- A graded equivalence between `P` and `Q` also intertwines `P.oppositePair L` and
`Q.oppositePair (e.centralizerEquiv L)`. -/
def oppositePairEquiv (e : GradedPairEquiv P Q) (L : P.centralizer) :
    GradedPairEquiv (P.oppositePair L) (Q.oppositePair (e.centralizerEquiv L)) where
  toLinearEquiv := e.toLinearEquiv
  mem_grade_iff' := e.mem_grade_iff'
  map_operator' v := by
    simp only [GradedPair.oppositePair_operator, coe_toLinearEquiv]
    exact (e.centralizerEquiv_apply_apply L v).symm

end GradedPairEquiv

/-! ### Restriction to centralizer-stable submodule models and actual images -/

namespace GradedPair

variable {S T : GradedCoordSpace} {d : StepDirection}

/-- Every element of `P.centralizer` preserves `LinearMap.range (P.operator ^ k)`. -/
theorem range_pow_mem_of_mem_centralizer (P : GradedPair S d) (k : ℕ)
    {L : Module.End ℂ S.Carrier} (hL : L ∈ P.centralizer) {v : S.Carrier}
    (hv : v ∈ LinearMap.range (P.operator ^ k)) :
    L v ∈ LinearMap.range (P.operator ^ k) := by
  obtain ⟨x, rfl⟩ := hv
  have h1 : L ∘ₗ P.operator = P.operator ∘ₗ L := (mem_centralizer_iff.1 hL).2
  have hpow : L ∘ₗ (P.operator ^ k) = (P.operator ^ k) ∘ₗ L := by
    induction k with
    | zero => simp [Module.End.one_eq_id]
    | succ j ih =>
      rw [pow_succ, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ih,
        LinearMap.comp_assoc, h1, ← LinearMap.comp_assoc]
  exact ⟨L x, (congrFun (congrArg DFunLike.coe hpow) x).symm⟩

/-- Every element of `P.centralizer` preserves `LinearMap.range P.operator`. -/
theorem range_operator_mem_of_mem_centralizer (P : GradedPair S d)
    {L : Module.End ℂ S.Carrier} (hL : L ∈ P.centralizer) {v : S.Carrier}
    (hv : v ∈ LinearMap.range P.operator) :
    L v ∈ LinearMap.range P.operator := by
  simpa using P.range_pow_mem_of_mem_centralizer 1 hL (by simpa using hv)

namespace SubmoduleModel

variable {P : GradedPair S d} {W : Submodule ℂ S.Carrier}

/-- Restrict elements of `P.centralizer` to any `P.centralizer`-stable submodule model `M`. -/
noncomputable def restrictCentralizer (M : P.SubmoduleModel W)
    (hW : ∀ L ∈ P.centralizer, ∀ v ∈ W, L v ∈ W) :
    P.centralizer →ₗ[ℂ] M.pair.centralizer where
  toFun L :=
    ⟨M.equiv.symm.toLinearMap ∘ₗ
        ((L : Module.End ℂ S.Carrier).restrict (hW L L.property)) ∘ₗ
        M.equiv.toLinearMap, by
      refine mem_centralizer_iff.2 ⟨LinearMap.isHomogeneous_def.2 fun a v hv ↦ ?_,
        LinearMap.ext fun v ↦ M.embed_injective ?_⟩
      · rw [← M.embed_mem_grade_iff]
        have hv' : M.embed v ∈ S.grade a := M.embed_mem_grade_iff.2 hv
        have himg : (L : Module.End ℂ S.Carrier) (M.embed v) ∈ S.grade (a + -d.step) :=
          (centralizer_isHomogeneous L).map_mem hv'
        simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, M.embed_equiv_symm_apply,
          LinearMap.restrict_apply, M.coe_equiv_apply] using himg
      · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, M.embed_operator,
          M.embed_equiv_symm_apply, LinearMap.restrict_apply, M.coe_equiv_apply,
          centralizer_operator_apply]⟩
  map_add' L₁ L₂ := Subtype.ext (LinearMap.ext fun v ↦ M.embed_injective (by simp))
  map_smul' c L := Subtype.ext (LinearMap.ext fun v ↦ M.embed_injective (by simp))

/-- Embedding the restricted centralizer element agrees with applying the ambient centralizer
element after embedding. -/
@[simp]
theorem embed_restrictCentralizer_apply (M : P.SubmoduleModel W)
    (hW : ∀ L ∈ P.centralizer, ∀ v ∈ W, L v ∈ W) (L : P.centralizer) (v : M.space.Carrier) :
    M.embed ((M.restrictCentralizer hW L : Module.End ℂ M.space.Carrier) v) =
      (L : Module.End ℂ S.Carrier) (M.embed v) := by
  simp [restrictCentralizer]

/-- Conjugation by a graded equivalence commutes with restriction to image models through the
induced image equivalence. -/
theorem restrictCentralizer_comp_centralizerEquiv {Q : GradedPair T d}
    (e : GradedPairEquiv P Q) (M : P.ImageModel) (N : Q.ImageModel) (L : P.centralizer) :
    (e.imageEquiv M N).centralizerEquiv
        (M.restrictCentralizer (fun _ hL _ hv ↦ P.range_operator_mem_of_mem_centralizer hL hv) L) =
      N.restrictCentralizer (fun _ hL _ hv ↦ Q.range_operator_mem_of_mem_centralizer hL hv)
        (e.centralizerEquiv L) := by
  refine Subtype.ext (LinearMap.ext fun w ↦ N.embed_injective ?_)
  have hemem : N.embed w = e (M.embed ((e.imageEquiv M N).symm w)) := by
    rw [← e.embed_imageEquiv_apply M N ((e.imageEquiv M N).symm w),
      GradedPairEquiv.apply_symm_apply]
  calc
    N.embed (((e.imageEquiv M N).centralizerEquiv
        (M.restrictCentralizer (fun _ hL _ hv ↦ P.range_operator_mem_of_mem_centralizer hL hv)
          L) : Module.End ℂ N.space.Carrier) w)
        = N.embed ((e.imageEquiv M N)
            ((M.restrictCentralizer
              (fun _ hL _ hv ↦ P.range_operator_mem_of_mem_centralizer hL hv) L :
              Module.End ℂ M.space.Carrier) ((e.imageEquiv M N).symm w))) := by
          rw [← (e.imageEquiv M N).apply_symm_apply w, GradedPairEquiv.centralizerEquiv_apply_apply,
            GradedPairEquiv.apply_symm_apply]
    _ = e ((L : Module.End ℂ S.Carrier) (M.embed ((e.imageEquiv M N).symm w))) := by simp
    _ = (e.centralizerEquiv L : Module.End ℂ T.Carrier)
          (e (M.embed ((e.imageEquiv M N).symm w))) := by
        rw [GradedPairEquiv.centralizerEquiv_apply_apply]
    _ = (e.centralizerEquiv L : Module.End ℂ T.Carrier) (N.embed w) := by rw [← hemem]
    _ = N.embed ((N.restrictCentralizer
          (fun _ hL _ hv ↦ Q.range_operator_mem_of_mem_centralizer hL hv)
          (e.centralizerEquiv L) : Module.End ℂ N.space.Carrier) w) := by simp

end SubmoduleModel

/-- Restriction of the opposite-degree centralizer of `P` to the chosen image model
`P.imageModel`. -/
noncomputable def restrictCentralizer (P : GradedPair S d) :
    P.centralizer →ₗ[ℂ] P.imageModel.pair.centralizer :=
  P.imageModel.restrictCentralizer fun _ hL _ hv ↦ P.range_operator_mem_of_mem_centralizer hL hv

@[simp]
theorem embed_restrictCentralizer_apply (P : GradedPair S d) (L : P.centralizer)
    (v : P.imageModel.space.Carrier) :
    P.imageModel.embed ((P.restrictCentralizer L : Module.End ℂ P.imageModel.space.Carrier) v) =
      (L : Module.End ℂ S.Carrier) (P.imageModel.embed v) :=
  P.imageModel.embed_restrictCentralizer_apply
    (fun _ hL _ hv ↦ P.range_operator_mem_of_mem_centralizer hL hv) L v

/-- Conjugation by a graded equivalence commutes with `restrictCentralizer` through the induced
equivalence between chosen image models. -/
theorem restrictCentralizer_centralizerEquiv {Q : GradedPair T d}
    (e : GradedPairEquiv P Q) (L : P.centralizer) :
    (e.imageEquiv P.imageModel Q.imageModel).centralizerEquiv (P.restrictCentralizer L) =
      Q.restrictCentralizer (e.centralizerEquiv L) :=
  SubmoduleModel.restrictCentralizer_comp_centralizerEquiv e P.imageModel Q.imageModel L

/-- When `P.operator = 0`, the image centralizer is trivial and `P.restrictCentralizer = 0`. -/
theorem restrictCentralizer_eq_zero_of_operator_eq_zero {P : GradedPair S d}
    (hP : P.operator = 0) :
    P.restrictCentralizer = 0 := by
  refine LinearMap.ext fun L ↦ Subtype.ext (LinearMap.ext fun v ↦ ?_)
  have hn : P.imageModel.space.n = 0 := (ImageModel.n_eq_zero_iff P.imageModel).2 hP
  have hsub : Subsingleton P.imageModel.space.Carrier :=
    ⟨fun x y ↦ funext fun i ↦ Fin.elim0 (hn ▸ i)⟩
  exact Subsingleton.elim _ _

/-- On the zero-dimensional coordinate space, the centralizer is trivial and restriction is zero. -/
theorem subsingleton_centralizer_of_n_eq_zero {P : GradedPair S d} (hn : S.n = 0) :
    Subsingleton P.centralizer := by
  have hcar : Subsingleton S.Carrier := ⟨fun x y ↦ funext fun i ↦ Fin.elim0 (hn ▸ i)⟩
  exact ⟨fun L₁ L₂ ↦ Subtype.ext (LinearMap.ext fun v ↦ Subsingleton.elim _ _)⟩

/-! ### Surjective centralizer image extension -/

section Extension

/-- On each grade `S.grade a`, there exists a linear map into `S.grade (a - d.step)` extending
`L'` on `LinearMap.range P.operator ⊓ S.grade a` and commuting with `P.operator` against `L'`. -/
private theorem exists_extensionOnGrade (P : GradedPair S d)
    (L' : Module.End ℂ (LinearMap.range P.operator))
    (hgrade : ∀ (a : ℤ) (v : LinearMap.range P.operator),
      (v : S.Carrier) ∈ S.grade a → (L' v : S.Carrier) ∈ S.grade (a - d.step))
    (hcomm : ∀ v : LinearMap.range P.operator,
      L' (P.operator.rangeRestrict (v : S.Carrier)) =
        P.operator.rangeRestrict (L' v : S.Carrier))
    (a : ℤ) :
    ∃ Lₐ : S.grade a →ₗ[ℂ] S.grade (a - d.step),
      (∀ (v : LinearMap.range P.operator) (hv : (v : S.Carrier) ∈ S.grade a),
        (Lₐ ⟨v, hv⟩ : S.Carrier) = L' v) ∧
      (∀ x : S.grade a,
        P.operator (Lₐ x : S.Carrier) = L' (P.operator.rangeRestrict (x : S.Carrier))) := by
  classical
  let Rₐ : Submodule ℂ (S.grade a) := (LinearMap.range P.operator).comap (S.grade a).subtype
  obtain ⟨Uₐ, hRU⟩ := Rₐ.exists_isCompl
  -- Restrict `P.operator` to a surjection `S.grade (a - d.step) ↠ Rₐ` and pick a right inverse.
  let Tₐ : S.grade (a - d.step) →ₗ[ℂ] Rₐ :=
    { toFun := fun x ↦
        ⟨⟨P.operator x, by simpa only [sub_add_cancel] using P.isHomogeneous.map_mem x.property⟩,
          LinearMap.mem_range_self _ _⟩
      map_add' := fun x y ↦ by ext; simp
      map_smul' := fun c x ↦ by ext; simp }
  have hTₐ : LinearMap.range Tₐ = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨⟨w, hwa⟩, hwr⟩ _
    have hw : w ∈ (S.grade (a - d.step)).map P.operator := by
      rw [← P.range_inf_grade_eq_map a]
      exact ⟨hwr, hwa⟩
    obtain ⟨x, hx, rfl⟩ := hw
    exact ⟨⟨x, hx⟩, by ext; rfl⟩
  let _ : Module.Projective ℂ ↥Rₐ := Module.Projective.of_basis (Basis.ofVectorSpace ℂ ↥Rₐ)
  obtain ⟨sₐ, hsₐ⟩ := Tₐ.exists_rightInverse_of_surjective hTₐ
  let φₐ : Rₐ →ₗ[ℂ] S.grade (a - d.step) :=
    { toFun := fun w ↦ ⟨L' ⟨w, w.property⟩, hgrade a ⟨w, w.property⟩ w.val.property⟩
      map_add' := fun w₁ w₂ ↦ Subtype.ext (by
        have hw : (⟨((w₁ + w₂ : Rₐ) : S.Carrier), (w₁ + w₂).property⟩ :
            LinearMap.range P.operator) = ⟨w₁, w₁.property⟩ + ⟨w₂, w₂.property⟩ := by
          apply Subtype.ext; simp
        have hL : (L' ⟨((w₁ + w₂ : Rₐ) : S.Carrier), (w₁ + w₂).property⟩ : S.Carrier) =
            (L' ⟨w₁, w₁.property⟩ : S.Carrier) + (L' ⟨w₂, w₂.property⟩ : S.Carrier) :=
          (congrArg (fun v : LinearMap.range P.operator ↦ (L' v : S.Carrier)) hw).trans
            (by rw [map_add, Submodule.coe_add])
        exact hL.trans (Submodule.coe_add _ _).symm)
      map_smul' := fun c w ↦ Subtype.ext (by
        have hw : (⟨((c • w : Rₐ) : S.Carrier), (c • w).property⟩ :
            LinearMap.range P.operator) = c • ⟨w, w.property⟩ := by
          apply Subtype.ext; simp
        have hL : (L' ⟨((c • w : Rₐ) : S.Carrier), (c • w).property⟩ : S.Carrier) =
            c • (L' ⟨w, w.property⟩ : S.Carrier) :=
          (congrArg (fun v : LinearMap.range P.operator ↦ (L' v : S.Carrier)) hw).trans
            (by rw [map_smul, Submodule.coe_smul])
        exact hL.trans (Submodule.coe_smul c _).symm) }
  let ψₐ : Uₐ →ₗ[ℂ] S.grade (a - d.step) :=
    { toFun := fun u ↦ sₐ ⟨⟨L' (P.operator.rangeRestrict (u : S.Carrier)), by
        have hu : P.operator (u : S.Carrier) ∈ S.grade (a + d.step) :=
          P.isHomogeneous.map_mem u.val.property
        have hl := hgrade (a + d.step) (P.operator.rangeRestrict (u : S.Carrier)) hu
        simpa only [add_sub_cancel_right] using hl⟩,
        (L' (P.operator.rangeRestrict (u : S.Carrier))).property⟩
      map_add' := fun u₁ u₂ ↦ by rw [← map_add sₐ]; congr 1; ext; simp
      map_smul' := fun c u ↦ by rw [← map_smul sₐ]; congr 1; ext; simp }
  refine ⟨LinearMap.ofIsCompl hRU φₐ ψₐ, ?_, ?_⟩
  · intro v hv
    have hvR : (⟨(v : S.Carrier), hv⟩ : S.grade a) ∈ Rₐ := v.property
    exact congrArg Subtype.val
      (LinearMap.ofIsCompl_apply_left hRU (φ := φₐ) (ψ := ψₐ) ⟨⟨v, hv⟩, hvR⟩)
  · intro x
    let lhs : S.grade a →ₗ[ℂ] S.Carrier :=
      P.operator ∘ₗ (S.grade (a - d.step)).subtype ∘ₗ LinearMap.ofIsCompl hRU φₐ ψₐ
    let rhs : S.grade a →ₗ[ℂ] S.Carrier :=
      (LinearMap.range P.operator).subtype ∘ₗ L' ∘ₗ P.operator.rangeRestrict ∘ₗ (S.grade a).subtype
    have hlhs : lhs = rhs := by
      rw [← LinearMap.ofIsCompl_eq' hRU rfl rfl (χ := lhs),
        ← LinearMap.ofIsCompl_eq' hRU rfl rfl (χ := rhs)]
      congr 1
      · refine LinearMap.ext fun r ↦ ?_
        simp only [lhs, rhs, LinearMap.comp_apply, Submodule.coe_subtype,
          LinearMap.ofIsCompl_apply_left]
        exact (congrArg Subtype.val (hcomm ⟨r, r.property⟩)).symm
      · refine LinearMap.ext fun u ↦ ?_
        simp only [lhs, rhs, LinearMap.comp_apply, Submodule.coe_subtype,
          LinearMap.ofIsCompl_apply_right, ψₐ, LinearMap.coe_mk, AddHom.coe_mk]
        let w : Rₐ := ⟨⟨L' (P.operator.rangeRestrict (u : S.Carrier)), by
          have hu : P.operator (u : S.Carrier) ∈ S.grade (a + d.step) :=
            P.isHomogeneous.map_mem u.val.property
          have hl := hgrade (a + d.step) (P.operator.rangeRestrict (u : S.Carrier)) hu
          simpa only [add_sub_cancel_right] using hl⟩,
          (L' (P.operator.rangeRestrict (u : S.Carrier))).property⟩
        have hs := congrArg (fun f : Rₐ →ₗ[ℂ] Rₐ ↦ ((f w : S.grade a) : S.Carrier)) hsₐ
        simpa [Tₐ, w] using hs
    exact congrFun (congrArg DFunLike.coe hlhs) x

end Extension

/-- Every opposite-degree commuting endomorphism on `LinearMap.range P.operator` extends to an
element of `P.centralizer`. -/
theorem centralizer_image_extension (P : GradedPair S d)
    (L' : Module.End ℂ (LinearMap.range P.operator))
    (hgrade : ∀ (a : ℤ) (v : LinearMap.range P.operator),
      (v : S.Carrier) ∈ S.grade a → (L' v : S.Carrier) ∈ S.grade (a - d.step))
    (hcomm : ∀ v : LinearMap.range P.operator,
      L' (P.operator.rangeRestrict (v : S.Carrier)) =
        P.operator.rangeRestrict (L' v : S.Carrier)) :
    ∃ L ∈ P.centralizer, ∀ v : LinearMap.range P.operator,
      L (v : S.Carrier) = (L' v : S.Carrier) := by
  classical
  let _ : DirectSum.Decomposition S.grade := S.isInternal_grade.chooseDecomposition
  choose g hg_ext hg_comm using fun a ↦ exists_extensionOnGrade P L' hgrade hcomm a
  let L : Module.End ℂ S.Carrier :=
    (DirectSum.toModule ℂ ℤ S.Carrier fun a ↦ (S.grade (a - d.step)).subtype ∘ₗ g a) ∘ₗ
      (DirectSum.decomposeLinearEquiv S.grade).toLinearMap
  have hL_grade (a : ℤ) (x : S.grade a) : L x = (g a x : S.Carrier) := by
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe,
      DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_coe]
    rw [← DirectSum.lof_eq_of ℂ, DirectSum.toModule_lof]
    rfl
  have hL_hom : LinearMap.IsHomogeneous L S.grade S.grade (-d.step) :=
    LinearMap.isHomogeneous_def.2 fun a x hx ↦ by
      rw [hL_grade a ⟨x, hx⟩, ← sub_eq_add_neg]
      exact (g a ⟨x, hx⟩).property
  have hL_range (x : S.Carrier) :
      L (P.operator x) = (L' (P.operator.rangeRestrict x) : S.Carrier) := by
    induction x using DirectSum.Decomposition.inductionOn S.grade with
    | zero => simp
    | @homogeneous a x =>
      have hmem : P.operator (x : S.Carrier) ∈ S.grade (a + d.step) :=
        P.isHomogeneous.map_mem x.property
      rw [hL_grade (a + d.step) ⟨P.operator x, hmem⟩]
      exact hg_ext (a + d.step) (P.operator.rangeRestrict (x : S.Carrier)) hmem
    | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
  have hPL_range (x : S.Carrier) :
      P.operator (L x) = (L' (P.operator.rangeRestrict x) : S.Carrier) := by
    induction x using DirectSum.Decomposition.inductionOn S.grade with
    | zero => simp
    | @homogeneous a x =>
      rw [hL_grade a x]
      exact hg_comm a x
    | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
  refine ⟨L, mem_centralizer_iff.2 ⟨hL_hom, LinearMap.ext fun x ↦ ?_⟩, fun ⟨_, x, rfl⟩ ↦ ?_⟩
  · exact (hL_range x).trans (hPL_range x).symm
  · exact hL_range x

namespace SubmoduleModel

variable {P : GradedPair S d}

/-- Restriction of the opposite-degree centralizer to any image model of `P` is surjective. -/
theorem restrictCentralizer_surjective (M : P.ImageModel) :
    Function.Surjective
      (M.restrictCentralizer fun _ hL _ hv ↦ P.range_operator_mem_of_mem_centralizer hL hv) := by
  intro L'
  let L'' : Module.End ℂ (LinearMap.range P.operator) :=
    M.equiv.toLinearMap ∘ₗ (L' : Module.End ℂ M.space.Carrier) ∘ₗ M.equiv.symm.toLinearMap
  have hgrade : ∀ (a : ℤ) (v : LinearMap.range P.operator),
      (v : S.Carrier) ∈ S.grade a → (L'' v : S.Carrier) ∈ S.grade (a - d.step) := by
    intro a v hv
    have hv' : M.equiv.symm v ∈ M.space.grade a := by
      rw [← M.embed_mem_grade_iff, M.embed_equiv_symm_apply]
      exact hv
    have hL' : (L' : Module.End ℂ M.space.Carrier) (M.equiv.symm v) ∈
        M.space.grade (a + -d.step) := (centralizer_isHomogeneous L').map_mem hv'
    simpa only [L'', LinearMap.comp_apply, LinearEquiv.coe_coe, M.coe_equiv_apply,
      M.embed_mem_grade_iff, sub_eq_add_neg] using hL'
  have hcomm : ∀ v : LinearMap.range P.operator,
      L'' (P.operator.rangeRestrict (v : S.Carrier)) =
        P.operator.rangeRestrict (L'' v : S.Carrier) := by
    intro v
    apply Subtype.ext
    have hr : P.operator.rangeRestrict (v : S.Carrier) =
        M.equiv (M.pair.operator (M.equiv.symm v)) := by
      apply Subtype.ext
      simp
    simp only [L'', LinearMap.comp_apply, LinearEquiv.coe_coe, hr, LinearEquiv.symm_apply_apply,
      M.coe_equiv_apply, centralizer_operator_apply, M.embed_operator]
    rfl
  obtain ⟨L, hL, hLext⟩ := P.centralizer_image_extension L'' hgrade hcomm
  refine ⟨⟨L, hL⟩, Subtype.ext (LinearMap.ext fun v ↦ M.embed_injective ?_)⟩
  have hv := hLext ⟨M.embed v, M.embed_mem v⟩
  have hsymm : M.equiv.symm ⟨M.embed v, M.embed_mem v⟩ = v :=
    M.embed_injective (by simp)
  rw [embed_restrictCentralizer_apply, hv]
  simp [L'', hsymm]

end SubmoduleModel

/-- Restriction of the opposite-degree centralizer to the chosen image model is surjective in
both step directions. -/
theorem restrictCentralizer_surjective (P : GradedPair S d) :
    Function.Surjective P.restrictCentralizer :=
  SubmoduleModel.restrictCentralizer_surjective P.imageModel

end GradedPair

end TauCeti
