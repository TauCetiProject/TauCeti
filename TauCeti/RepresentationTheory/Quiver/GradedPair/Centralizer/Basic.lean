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

* `TauCeti.GradedPair.SubmoduleModel.centralizerEquiv_restrictCentralizer`: conjugation
  commutes with restriction through the induced image equivalence.
* `TauCeti.GradedPair.SubmoduleModel.restrictCentralizer_map`: restriction commutes with
  transporting a centralizer-stable submodule model along a graded equivalence.
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
theorem isHomogeneous_coe_centralizer {P : GradedPair S d} (L : P.centralizer) :
    LinearMap.IsHomogeneous (L : Module.End ℂ S.Carrier) S.grade S.grade (-d.step) :=
  (mem_centralizer_iff.1 L.property).1

/-- A member of `P.centralizer` commutes with `P.operator`. -/
theorem coe_centralizer_comp_operator_comm {P : GradedPair S d} (L : P.centralizer) :
    (L : Module.End ℂ S.Carrier) ∘ₗ P.operator =
      P.operator ∘ₗ (L : Module.End ℂ S.Carrier) :=
  (mem_centralizer_iff.1 L.property).2

/-- Pointwise commutation of a centralizer element with `P.operator`. -/
@[simp]
theorem coe_centralizer_operator_apply_comm {P : GradedPair S d} (L : P.centralizer)
    (v : S.Carrier) :
    (L : Module.End ℂ S.Carrier) (P.operator v) =
      P.operator ((L : Module.End ℂ S.Carrier) v) :=
  congrFun (congrArg DFunLike.coe (coe_centralizer_comp_operator_comm L)) v

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
    simpa only [StepDirection.step_reverse] using isHomogeneous_coe_centralizer L

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
  exact ⟨P.isHomogeneous, (coe_centralizer_comp_operator_comm L).symm⟩

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

private theorem conj_operator (e : GradedPairEquiv P Q) :
    e.toLinearEquiv.conj P.operator = Q.operator :=
  LinearMap.ext fun v ↦ by
    rw [LinearEquiv.conj_apply_apply, coe_toLinearEquiv, ← toLinearEquiv_symm,
      coe_toLinearEquiv, e.map_operator, e.apply_symm_apply]

private theorem conj_mem_centralizer (e : GradedPairEquiv P Q) {K : Module.End ℂ S.Carrier}
    (hK : K ∈ P.centralizer) :
    e.toLinearEquiv.conj K ∈ Q.centralizer := by
  obtain ⟨hKhom, hKcomm⟩ := GradedPair.mem_centralizer_iff.1 hK
  refine GradedPair.mem_centralizer_iff.2 ⟨LinearMap.isHomogeneous_def.2 fun a v hv ↦ ?_, ?_⟩
  · rw [LinearEquiv.conj_apply_apply, coe_toLinearEquiv, ← toLinearEquiv_symm, coe_toLinearEquiv,
      e.mem_grade_iff]
    exact hKhom.map_mem (e.symm.mem_grade_iff.2 hv)
  · rw [← e.conj_operator, ← LinearEquiv.conj_comp, ← LinearEquiv.conj_comp, hKcomm]

/-- Conjugation by a graded equivalence maps `P.centralizer` onto `Q.centralizer`. -/
theorem map_centralizer (e : GradedPairEquiv P Q) :
    P.centralizer.map (e.toLinearEquiv.conj : Module.End ℂ S.Carrier →ₗ[ℂ] Module.End ℂ T.Carrier) =
      Q.centralizer := by
  refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun _ hK ↦ e.conj_mem_centralizer hK)
    fun L hL ↦ ⟨e.symm.toLinearEquiv.conj L, e.symm.conj_mem_centralizer hL, ?_⟩
  simp [toLinearEquiv_symm]

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

/-- `e` intertwines `L` with its conjugate `e.centralizerEquiv L`. -/
theorem centralizerEquiv_apply_apply (e : GradedPairEquiv P Q) (L : P.centralizer)
    (v : S.Carrier) :
    (e.centralizerEquiv L : Module.End ℂ T.Carrier) (e v) =
      e ((L : Module.End ℂ S.Carrier) v) := by
  rw [coe_centralizerEquiv_apply, LinearEquiv.conj_apply_apply, coe_toLinearEquiv,
    ← toLinearEquiv_symm, coe_toLinearEquiv, e.symm_apply_apply]

/-- Centralizer conjugation preserves inverses. -/
@[simp]
theorem centralizerEquiv_symm (e : GradedPairEquiv P Q) :
    e.centralizerEquiv.symm = e.symm.centralizerEquiv := by
  refine LinearEquiv.ext fun L ↦ e.centralizerEquiv.injective (Subtype.ext ?_)
  simp [coe_centralizerEquiv_apply, toLinearEquiv_symm]

/-- Centralizer conjugation along the identity equivalence is the identity. -/
@[simp]
theorem centralizerEquiv_refl (P : GradedPair S d) :
    (refl P).centralizerEquiv = LinearEquiv.refl ℂ P.centralizer := by
  refine LinearEquiv.ext fun L ↦ Subtype.ext ?_
  have hrefl : (refl P).toLinearEquiv = LinearEquiv.refl ℂ S.Carrier :=
    LinearEquiv.ext refl_apply
  rw [coe_centralizerEquiv_apply, LinearEquiv.refl_apply, hrefl, LinearEquiv.conj_refl]

/-- Centralizer conjugation preserves composition of graded equivalences. -/
theorem centralizerEquiv_trans (e : GradedPairEquiv P Q) (f : GradedPairEquiv Q R) :
    (e.trans f).centralizerEquiv = e.centralizerEquiv.trans f.centralizerEquiv := by
  refine LinearEquiv.ext fun L ↦ Subtype.ext ?_
  have htrans : (e.trans f).toLinearEquiv = e.toLinearEquiv.trans f.toLinearEquiv :=
    LinearEquiv.ext (trans_apply e f)
  simp only [LinearEquiv.trans_apply, coe_centralizerEquiv_apply, htrans, ← LinearEquiv.conj_trans]

/-- A graded equivalence between `P` and `Q` also intertwines `P.oppositePair L` and
`Q.oppositePair (e.centralizerEquiv L)`. -/
def oppositePairEquiv (e : GradedPairEquiv P Q) (L : P.centralizer) :
    GradedPairEquiv (P.oppositePair L) (Q.oppositePair (e.centralizerEquiv L)) where
  toLinearEquiv := e.toLinearEquiv
  mem_grade_iff' := e.mem_grade_iff'
  map_operator' v := by
    simp only [GradedPair.oppositePair_operator, coe_toLinearEquiv]
    exact (e.centralizerEquiv_apply_apply L v).symm

/-- Evaluating `e.oppositePairEquiv L` on a vector agrees with applying `e`. -/
@[simp]
theorem oppositePairEquiv_apply (e : GradedPairEquiv P Q) (L : P.centralizer) (v : S.Carrier) :
    e.oppositePairEquiv L v = e v :=
  (rfl)

end GradedPairEquiv

/-! ### Restriction to centralizer-stable submodule models and actual images -/

namespace GradedPair

variable {S T : GradedCoordSpace} {d : StepDirection}

/-- Any endomorphism commuting with `P.operator` preserves `LinearMap.range (P.operator ^ k)`. -/
theorem apply_mem_range_pow_of_commute (P : GradedPair S d) (k : ℕ)
    {L : Module.End ℂ S.Carrier} (hL : Commute L P.operator) {v : S.Carrier}
    (hv : v ∈ LinearMap.range (P.operator ^ k)) :
    L v ∈ LinearMap.range (P.operator ^ k) := by
  have hsem : Function.Semiconj (P.operator ^ k) L L := fun x ↦ by
    simpa only [mul_apply_eq_comp] using
      (congrArg (fun f : Module.End ℂ S.Carrier ↦ f x) (hL.pow_right k).eq).symm
  exact hsem.mapsTo_range hv

/-- Any endomorphism commuting with `P.operator` preserves `LinearMap.range P.operator`. -/
theorem apply_mem_range_operator_of_commute (P : GradedPair S d)
    {L : Module.End ℂ S.Carrier} (hL : Commute L P.operator) {v : S.Carrier}
    (hv : v ∈ LinearMap.range P.operator) :
    L v ∈ LinearMap.range P.operator := by
  have hv1 : v ∈ LinearMap.range (P.operator ^ 1) := by simpa only [pow_one] using hv
  simpa only [pow_one] using P.apply_mem_range_pow_of_commute 1 hL hv1

/-- Every element of `P.centralizer` preserves `LinearMap.range P.operator`. -/
theorem apply_mem_range_operator_of_mem_centralizer (P : GradedPair S d) :
    ∀ L ∈ P.centralizer, ∀ v ∈ LinearMap.range P.operator, L v ∈ LinearMap.range P.operator :=
  fun _ hL _ hv ↦ P.apply_mem_range_operator_of_commute (mem_centralizer_iff.1 hL).2 hv

namespace SubmoduleModel

variable {P : GradedPair S d} {W : Submodule ℂ S.Carrier}

/-- Restrict elements of `P.centralizer` to any `P.centralizer`-stable submodule model `M`. -/
noncomputable def restrictCentralizer (M : P.SubmoduleModel W)
    (hW : ∀ L ∈ P.centralizer, ∀ v ∈ W, L v ∈ W) :
    P.centralizer →ₗ[ℂ] M.pair.centralizer where
  toFun L :=
    ⟨M.equiv.symm.conj ((L : Module.End ℂ S.Carrier).restrict (hW L L.property)), by
      have hPW : ∀ v ∈ W, P.operator v ∈ W := fun w hw ↦ by
        obtain ⟨u, rfl⟩ := M.mem_iff_exists_embed_eq.1 hw
        simpa only [← M.embed_operator] using M.embed_mem _
      have hPconj : M.equiv.symm.conj (P.operator.restrict hPW) = M.pair.operator :=
        LinearMap.ext fun v ↦ M.embed_injective (by simp)
      have hcomm : Commute ((L : Module.End ℂ S.Carrier).restrict (hW L L.property))
          (P.operator.restrict hPW) :=
        LinearMap.restrict_commute (coe_centralizer_comp_operator_comm L) (hW L L.property) hPW
      refine mem_centralizer_iff.2 ⟨LinearMap.isHomogeneous_def.2 fun a v hv ↦ ?_, ?_⟩
      · rw [← M.embed_mem_grade_iff]
        have hv' : M.embed v ∈ S.grade a := M.embed_mem_grade_iff.2 hv
        have himg : (L : Module.End ℂ S.Carrier) (M.embed v) ∈ S.grade (a + -d.step) :=
          (isHomogeneous_coe_centralizer L).map_mem hv'
        simpa only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
          M.embed_equiv_symm_apply, LinearMap.restrict_apply, M.coe_equiv_apply] using himg
      · rw [← hPconj, ← LinearEquiv.conj_comp, ← LinearEquiv.conj_comp]
        exact congrArg M.equiv.symm.conj hcomm.eq⟩
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

/-- Centralizer stability of a submodule `W` transports along a graded equivalence `e` to the
image submodule `W.map e`. -/
theorem apply_mem_map_of_mem_centralizer {Q : GradedPair T d} (e : GradedPairEquiv P Q)
    (hW : ∀ L ∈ P.centralizer, ∀ v ∈ W, L v ∈ W) :
    ∀ L ∈ Q.centralizer,
      ∀ w ∈ W.map (e.toLinearEquiv : S.Carrier →ₗ[ℂ] T.Carrier),
        L w ∈ W.map (e.toLinearEquiv : S.Carrier →ₗ[ℂ] T.Carrier) := by
  rintro L hL _ ⟨v, hv, rfl⟩
  refine ⟨(e.symm.centralizerEquiv ⟨L, hL⟩ : Module.End ℂ S.Carrier) v,
    hW _ (e.symm.centralizerEquiv ⟨L, hL⟩).property v hv, ?_⟩
  simp

/-- Transporting a centralizer-stable submodule model `M` along `e : GradedPairEquiv P Q`
identifies restriction of `e.centralizerEquiv L` on `M.map e` with restriction of `L` on `M`. -/
theorem restrictCentralizer_map (M : P.SubmoduleModel W) {Q : GradedPair T d}
    (e : GradedPairEquiv P Q) (hW : ∀ L ∈ P.centralizer, ∀ v ∈ W, L v ∈ W)
    (L : P.centralizer) :
    (M.map e).restrictCentralizer (apply_mem_map_of_mem_centralizer e hW)
        (e.centralizerEquiv L) =
      M.restrictCentralizer hW L := by
  refine Subtype.ext (LinearMap.ext fun v ↦ (M.map e).embed_injective ?_)
  rw [embed_restrictCentralizer_apply]
  exact (GradedPairEquiv.centralizerEquiv_apply_apply e L (M.embed v)).trans
    (congrArg e (M.embed_restrictCentralizer_apply hW L v).symm)

/-- Conjugation by a graded equivalence commutes with restriction to image models through the
induced image equivalence. -/
theorem centralizerEquiv_restrictCentralizer {Q : GradedPair T d}
    (e : GradedPairEquiv P Q) (M : P.ImageModel) (N : Q.ImageModel) (L : P.centralizer) :
    (e.imageEquiv M N).centralizerEquiv
        (M.restrictCentralizer P.apply_mem_range_operator_of_mem_centralizer L) =
      N.restrictCentralizer Q.apply_mem_range_operator_of_mem_centralizer
        (e.centralizerEquiv L) := by
  refine Subtype.ext (LinearMap.ext fun w ↦ N.embed_injective ?_)
  have hemem : N.embed w = e (M.embed ((e.imageEquiv M N).symm w)) := by
    rw [← e.embed_imageEquiv_apply M N ((e.imageEquiv M N).symm w),
      GradedPairEquiv.apply_symm_apply]
  calc
    N.embed (((e.imageEquiv M N).centralizerEquiv
        (M.restrictCentralizer P.apply_mem_range_operator_of_mem_centralizer L) :
        Module.End ℂ N.space.Carrier) w)
        = N.embed ((e.imageEquiv M N)
            ((M.restrictCentralizer P.apply_mem_range_operator_of_mem_centralizer L :
              Module.End ℂ M.space.Carrier) ((e.imageEquiv M N).symm w))) := by
          rw [← (e.imageEquiv M N).apply_symm_apply w, GradedPairEquiv.centralizerEquiv_apply_apply,
            GradedPairEquiv.apply_symm_apply]
    _ = e ((L : Module.End ℂ S.Carrier) (M.embed ((e.imageEquiv M N).symm w))) := by simp
    _ = (e.centralizerEquiv L : Module.End ℂ T.Carrier)
          (e (M.embed ((e.imageEquiv M N).symm w))) := by
        rw [GradedPairEquiv.centralizerEquiv_apply_apply]
    _ = (e.centralizerEquiv L : Module.End ℂ T.Carrier) (N.embed w) := by rw [← hemem]
    _ = N.embed ((N.restrictCentralizer Q.apply_mem_range_operator_of_mem_centralizer
          (e.centralizerEquiv L) : Module.End ℂ N.space.Carrier) w) := by simp

end SubmoduleModel

/-- Restriction of the opposite-degree centralizer of `P` to the chosen image model
`P.imageModel`. -/
noncomputable def restrictCentralizer (P : GradedPair S d) :
    P.centralizer →ₗ[ℂ] P.imageModel.pair.centralizer :=
  P.imageModel.restrictCentralizer P.apply_mem_range_operator_of_mem_centralizer

@[simp]
theorem embed_restrictCentralizer_apply (P : GradedPair S d) (L : P.centralizer)
    (v : P.imageModel.space.Carrier) :
    P.imageModel.embed ((P.restrictCentralizer L : Module.End ℂ P.imageModel.space.Carrier) v) =
      (L : Module.End ℂ S.Carrier) (P.imageModel.embed v) :=
  P.imageModel.embed_restrictCentralizer_apply P.apply_mem_range_operator_of_mem_centralizer L v

/-- Conjugation by a graded equivalence commutes with `restrictCentralizer` through the induced
equivalence between chosen image models. -/
theorem centralizerEquiv_restrictCentralizer {Q : GradedPair T d}
    (e : GradedPairEquiv P Q) (L : P.centralizer) :
    (e.imageEquiv P.imageModel Q.imageModel).centralizerEquiv (P.restrictCentralizer L) =
      Q.restrictCentralizer (e.centralizerEquiv L) :=
  SubmoduleModel.centralizerEquiv_restrictCentralizer e P.imageModel Q.imageModel L

/-- When `P.operator = 0`, `P.restrictCentralizer = 0`. -/
theorem restrictCentralizer_eq_zero_of_operator_eq_zero {P : GradedPair S d}
    (hP : P.operator = 0) :
    P.restrictCentralizer = 0 := by
  have : Subsingleton P.imageModel.space.Carrier :=
    GradedCoordSpace.subsingleton_carrier_of_n_eq_zero
      ((ImageModel.n_eq_zero_iff P.imageModel).2 hP)
  exact Subsingleton.elim _ _

/-- On the zero-dimensional coordinate space, `P.centralizer` is a subsingleton. -/
theorem subsingleton_centralizer_of_n_eq_zero {P : GradedPair S d} (hn : S.n = 0) :
    Subsingleton P.centralizer := by
  have : Subsingleton S.Carrier := GradedCoordSpace.subsingleton_carrier_of_n_eq_zero hn
  infer_instance

/-! ### Surjective centralizer image extension -/

section Extension

/-- An opposite-degree map `L'` on `range P.operator` sends `rangeRestrict u` back into `S.grade a`
whenever `u ∈ S.grade a`. -/
private theorem extensionOnGrade_rangeRestrict_mem (P : GradedPair S d)
    (L' : Module.End ℂ (LinearMap.range P.operator))
    (hgrade : ∀ (a : ℤ) (v : LinearMap.range P.operator),
      (v : S.Carrier) ∈ S.grade a → (L' v : S.Carrier) ∈ S.grade (a - d.step))
    {a : ℤ} {u : S.Carrier} (hu : u ∈ S.grade a) :
    (L' (P.operator.rangeRestrict u) : S.Carrier) ∈ S.grade a := by
  have hPu : P.operator u ∈ S.grade (a + d.step) := P.isHomogeneous.map_mem hu
  simpa only [add_sub_cancel_right] using hgrade (a + d.step) (P.operator.rangeRestrict u) hPu

/-- Restriction of `P.operator` as a linear map from `S.grade (a - d.step)` to the range part
`Rₐ = (LinearMap.range P.operator).comap (S.grade a).subtype`. -/
private noncomputable def extensionGradeOperator (P : GradedPair S d) (a : ℤ) :
    S.grade (a - d.step) →ₗ[ℂ] (LinearMap.range P.operator).comap (S.grade a).subtype :=
  LinearMap.codRestrict ((LinearMap.range P.operator).comap (S.grade a).subtype)
    (LinearMap.codRestrict (S.grade a) (P.operator.domRestrict (S.grade (a - d.step)))
      fun x ↦ by
        simpa only [LinearMap.domRestrict_apply, sub_add_cancel] using
          P.isHomogeneous.map_mem x.property)
    fun x ↦ by
      simpa only [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.codRestrict_apply,
        LinearMap.domRestrict_apply] using LinearMap.mem_range_self P.operator (x : S.Carrier)

private theorem coe_extensionGradeOperator (P : GradedPair S d) (a : ℤ)
    (z : S.grade (a - d.step)) :
    ((extensionGradeOperator P a z : S.grade a) : S.Carrier) = P.operator (z : S.Carrier) :=
  (congrArg Subtype.val (LinearMap.codRestrict_apply _ _ z)).trans
    ((LinearMap.codRestrict_apply _ _ z).trans (LinearMap.domRestrict_apply _ _ _))

/-- `extensionGradeOperator P a` is surjective onto `Rₐ`, using `range_inf_grade_eq_map`. -/
private theorem range_extensionGradeOperator (P : GradedPair S d) (a : ℤ) :
    LinearMap.range (extensionGradeOperator P a) = ⊤ := by
  rw [extensionGradeOperator, LinearMap.range_codRestrict, LinearMap.range_codRestrict,
    LinearMap.range_domRestrict, ← P.range_inf_grade_eq_map a, Submodule.comap_inf,
    Submodule.comap_subtype_self, inf_top_eq, Submodule.comap_subtype_self]

/-- Inclusion of the range part `Rₐ = (LinearMap.range P.operator).comap (S.grade a).subtype`
into `LinearMap.range P.operator`. -/
private noncomputable def extensionInclR (P : GradedPair S d) (a : ℤ) :
    (LinearMap.range P.operator).comap (S.grade a).subtype →ₗ[ℂ] LinearMap.range P.operator :=
  LinearMap.codRestrict (LinearMap.range P.operator)
    ((S.grade a).subtype ∘ₗ ((LinearMap.range P.operator).comap (S.grade a).subtype).subtype)
    fun w ↦ w.property

private theorem coe_extensionInclR (P : GradedPair S d) (a : ℤ)
    (r : (LinearMap.range P.operator).comap (S.grade a).subtype) :
    (extensionInclR P a r : S.Carrier) = ((r : S.grade a) : S.Carrier) :=
  (LinearMap.codRestrict_apply _ _ r).trans
    (by simp only [LinearMap.comp_apply, Submodule.coe_subtype])

/-- Restriction of `L'` to the range part `Rₐ`, landing in `S.grade (a - d.step)`. -/
private noncomputable def extensionPhi (P : GradedPair S d)
    (L' : Module.End ℂ (LinearMap.range P.operator))
    (hgrade : ∀ (a : ℤ) (v : LinearMap.range P.operator),
      (v : S.Carrier) ∈ S.grade a → (L' v : S.Carrier) ∈ S.grade (a - d.step))
    (a : ℤ) :
    (LinearMap.range P.operator).comap (S.grade a).subtype →ₗ[ℂ] S.grade (a - d.step) :=
  LinearMap.codRestrict (S.grade (a - d.step))
    ((LinearMap.range P.operator).subtype ∘ₗ L' ∘ₗ extensionInclR P a)
    fun w ↦ hgrade a (extensionInclR P a w) w.val.property

private theorem coe_extensionPhi (P : GradedPair S d)
    (L' : Module.End ℂ (LinearMap.range P.operator))
    (hgrade : ∀ (a : ℤ) (v : LinearMap.range P.operator),
      (v : S.Carrier) ∈ S.grade a → (L' v : S.Carrier) ∈ S.grade (a - d.step))
    (a : ℤ) (r : (LinearMap.range P.operator).comap (S.grade a).subtype) :
    (extensionPhi P L' hgrade a r : S.Carrier) = (L' (extensionInclR P a r) : S.Carrier) :=
  (LinearMap.codRestrict_apply _ _ r).trans
    (by simp only [LinearMap.comp_apply, Submodule.coe_subtype])

/-- Lift of `L' ∘ P.operator.rangeRestrict` from a complement `Uₐ ⊆ S.grade a` to `Rₐ`. -/
private noncomputable def extensionLiftU (P : GradedPair S d)
    (L' : Module.End ℂ (LinearMap.range P.operator))
    (hgrade : ∀ (a : ℤ) (v : LinearMap.range P.operator),
      (v : S.Carrier) ∈ S.grade a → (L' v : S.Carrier) ∈ S.grade (a - d.step))
    {a : ℤ} (Uₐ : Submodule ℂ (S.grade a)) :
    Uₐ →ₗ[ℂ] (LinearMap.range P.operator).comap (S.grade a).subtype :=
  LinearMap.codRestrict ((LinearMap.range P.operator).comap (S.grade a).subtype)
    (LinearMap.codRestrict (S.grade a)
      ((LinearMap.range P.operator).subtype ∘ₗ L' ∘ₗ P.operator.rangeRestrict ∘ₗ
        (S.grade a).subtype ∘ₗ Uₐ.subtype)
      fun u ↦ extensionOnGrade_rangeRestrict_mem P L' hgrade u.val.property)
    fun u ↦ (L' (P.operator.rangeRestrict ((u : S.grade a) : S.Carrier))).property

private theorem coe_extensionLiftU (P : GradedPair S d)
    (L' : Module.End ℂ (LinearMap.range P.operator))
    (hgrade : ∀ (a : ℤ) (v : LinearMap.range P.operator),
      (v : S.Carrier) ∈ S.grade a → (L' v : S.Carrier) ∈ S.grade (a - d.step))
    {a : ℤ} {Uₐ : Submodule ℂ (S.grade a)} (w : Uₐ) :
    ((extensionLiftU P L' hgrade Uₐ w : S.grade a) : S.Carrier) =
      (L' (P.operator.rangeRestrict ((w : S.grade a) : S.Carrier)) : S.Carrier) :=
  (congrArg Subtype.val (LinearMap.codRestrict_apply _ _ w)).trans
    ((LinearMap.codRestrict_apply _ _ w).trans
      (by simp only [LinearMap.comp_apply, Submodule.coe_subtype]))

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
  -- Split `S.grade a` into the range part `Rₐ` and a complement `Uₐ`, and pick a right inverse
  -- `sₐ` to `extensionGradeOperator P a : S.grade (a - d.step) ↠ Rₐ`.
  let Rₐ : Submodule ℂ (S.grade a) := (LinearMap.range P.operator).comap (S.grade a).subtype
  obtain ⟨Uₐ, hRU⟩ := Rₐ.exists_isCompl
  let _ : Module.Free ℂ ↥Rₐ := Module.Free.of_divisionRing ℂ ↥Rₐ
  obtain ⟨sₐ, hsₐ⟩ := (extensionGradeOperator P a).exists_rightInverse_of_surjective
    (range_extensionGradeOperator P a)
  let φₐ := extensionPhi P L' hgrade a
  let liftU := extensionLiftU P L' hgrade Uₐ
  let ψₐ : Uₐ →ₗ[ℂ] S.grade (a - d.step) := sₐ ∘ₗ liftU
  refine ⟨LinearMap.ofIsCompl hRU φₐ ψₐ, ?_, ?_⟩
  · intro v hv
    have hvR : (⟨(v : S.Carrier), hv⟩ : S.grade a) ∈ Rₐ := v.property
    have hleft := congrArg Subtype.val
      (LinearMap.ofIsCompl_apply_left hRU (φ := φₐ) (ψ := ψₐ) ⟨⟨v, hv⟩, hvR⟩)
    have hincv : extensionInclR P a ⟨⟨(v : S.Carrier), hv⟩, hvR⟩ = v :=
      Subtype.ext (coe_extensionInclR P a ⟨⟨(v : S.Carrier), hv⟩, hvR⟩)
    exact hleft.trans ((coe_extensionPhi P L' hgrade a ⟨⟨(v : S.Carrier), hv⟩, hvR⟩).trans
      (by rw [hincv]))
  · intro x
    have hr (r : Rₐ) :
        P.operator ((φₐ r : S.grade (a - d.step)) : S.Carrier) =
          L' (P.operator.rangeRestrict ((r : S.grade a) : S.Carrier)) := by
      have hc := congrArg Subtype.val (hcomm (extensionInclR P a r))
      have hp :
          (P.operator.rangeRestrict (L' (extensionInclR P a r) : S.Carrier) : S.Carrier) =
            P.operator (L' (extensionInclR P a r) : S.Carrier) :=
        LinearMap.codRestrict_apply _ _ _
      rw [coe_extensionPhi, ← coe_extensionInclR P a r, ← hp]
      exact hc.symm
    have hu (u : Uₐ) :
        P.operator ((ψₐ u : S.grade (a - d.step)) : S.Carrier) =
          L' (P.operator.rangeRestrict ((u : S.grade a) : S.Carrier)) := by
      have hs := congrArg
        (fun f : Rₐ →ₗ[ℂ] Rₐ ↦ ((f (liftU u) : S.grade a) : S.Carrier)) hsₐ
      rw [LinearMap.comp_apply, LinearMap.id_apply, coe_extensionGradeOperator,
        coe_extensionLiftU] at hs
      exact hs
    obtain ⟨r, u, hru, _⟩ := Submodule.existsUnique_add_of_isCompl hRU x
    rw [← hru]
    simp only [Submodule.coe_add, map_add, LinearMap.ofIsCompl_apply_left,
      LinearMap.ofIsCompl_apply_right, hr, hu]

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
    rw [← DirectSum.lof_eq_of ℂ, DirectSum.toModule_lof, LinearMap.comp_apply,
      Submodule.coe_subtype]
  have hL_hom : LinearMap.IsHomogeneous L S.grade S.grade (-d.step) :=
    LinearMap.isHomogeneous_def.2 fun a x hx ↦ by
      rw [hL_grade a ⟨x, hx⟩, ← sub_eq_add_neg]
      exact (g a ⟨x, hx⟩).property
  have hL_range : L ∘ₗ P.operator =
      (LinearMap.range P.operator).subtype ∘ₗ L' ∘ₗ P.operator.rangeRestrict := by
    refine DirectSum.decompose_lhom_ext S.grade fun a ↦ LinearMap.ext fun x ↦ ?_
    have hmem : P.operator (x : S.Carrier) ∈ S.grade (a + d.step) :=
      P.isHomogeneous.map_mem x.property
    simp only [LinearMap.comp_apply, Submodule.coe_subtype]
    rw [hL_grade (a + d.step) ⟨P.operator x, hmem⟩]
    exact hg_ext (a + d.step) (P.operator.rangeRestrict (x : S.Carrier)) hmem
  have hPL_range : P.operator ∘ₗ L =
      (LinearMap.range P.operator).subtype ∘ₗ L' ∘ₗ P.operator.rangeRestrict := by
    refine DirectSum.decompose_lhom_ext S.grade fun a ↦ LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.comp_apply, Submodule.coe_subtype]
    rw [hL_grade a x]
    exact hg_comm a x
  refine ⟨L, mem_centralizer_iff.2 ⟨hL_hom, hL_range.trans hPL_range.symm⟩, fun ⟨_, x, rfl⟩ ↦ ?_⟩
  exact congrFun (congrArg DFunLike.coe hL_range) x

namespace SubmoduleModel

variable {P : GradedPair S d}

/-- Restriction of the opposite-degree centralizer to any image model of `P` is surjective. -/
theorem restrictCentralizer_surjective (M : P.ImageModel) :
    Function.Surjective
      (M.restrictCentralizer P.apply_mem_range_operator_of_mem_centralizer) := by
  intro L'
  let L'' : Module.End ℂ (LinearMap.range P.operator) :=
    M.equiv.conj (L' : Module.End ℂ M.space.Carrier)
  have hgrade : ∀ (a : ℤ) (v : LinearMap.range P.operator),
      (v : S.Carrier) ∈ S.grade a → (L'' v : S.Carrier) ∈ S.grade (a - d.step) := by
    intro a v hv
    have hv' : M.equiv.symm v ∈ M.space.grade a := by
      rw [← M.embed_mem_grade_iff, M.embed_equiv_symm_apply]
      exact hv
    have hL' : (L' : Module.End ℂ M.space.Carrier) (M.equiv.symm v) ∈
        M.space.grade (a + -d.step) := (isHomogeneous_coe_centralizer L').map_mem hv'
    simpa only [L'', LinearEquiv.conj_apply_apply, M.coe_equiv_apply,
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
    simp only [L'', hr, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply,
      M.coe_equiv_apply, coe_centralizer_operator_apply_comm, M.embed_operator,
      LinearMap.codRestrict_apply]
  obtain ⟨L, hL, hLext⟩ := P.centralizer_image_extension L'' hgrade hcomm
  refine ⟨⟨L, hL⟩, Subtype.ext (LinearMap.ext fun v ↦ M.embed_injective ?_)⟩
  have hv := hLext ⟨M.embed v, M.embed_mem v⟩
  have hsymm : M.equiv.symm ⟨M.embed v, M.embed_mem v⟩ = v :=
    M.embed_injective (by simp)
  rw [embed_restrictCentralizer_apply, hv]
  simp [L'', LinearEquiv.conj_apply_apply, hsymm]

end SubmoduleModel

/-- Restriction of the opposite-degree centralizer to the chosen image model is surjective in
both step directions. -/
theorem restrictCentralizer_surjective (P : GradedPair S d) :
    Function.Surjective P.restrictCentralizer :=
  SubmoduleModel.restrictCentralizer_surjective P.imageModel

end GradedPair

end TauCeti
