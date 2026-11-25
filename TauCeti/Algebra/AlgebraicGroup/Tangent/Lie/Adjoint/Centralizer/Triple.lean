/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Basic
public import TauCeti.Algebra.Lie.Sl2.SlodowySlice.Basic
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Dimension
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.BasePoints
import TauCeti.Algebra.Lie.Sl2.Centralizer

/-!
# The centralizer of an `sl₂` triple and its action on the Slodowy slice

Let `G = Spec H` be an affine group over a field `k` with Lie algebra `𝔤`, modelled as the dual of
the augmentation cotangent space. For `h, e, f ∈ 𝔤` the centralizer `C_G(h, e, f)` is the
intersection `C_G(h) ∩ C_G(e) ∩ C_G(f)` of the centralizers of the three elements
(`TauCeti.tripleCentralizerHopfIdeal`), a closed subgroup scheme of `G`. Its points with values in
any commutative `k`-algebra are the points whose adjoint action fixes `h`, `e` and `f`, and its Lie
algebra is `ker (ad h) ∩ ker (ad e) ∩ ker (ad f)`.

Every point of `G` acts on `𝔤` by a Lie algebra automorphism, so `C_G(x) ∩ C_G(y)` lies in
`C_G(⁅x, y⁆)` (`TauCeti.centralizerHopfIdeal_lie_le_sup`). For an `sl₂` triple `(h, e, f)`, where
`h = ⁅e, f⁆`, the centralizer of the triple is therefore `C_G(e) ∩ C_G(f)`, over every field and as
schemes. Over an algebraically closed field of characteristic zero it is also `C_G(h) ∩ C_G(e)`
(`IsSl2Triple.tripleCentralizerHopfIdeal_eq_sup`): a rational point fixing `h` and `e` carries `f`
to an element completing `(h, e)` to an `sl₂` triple, which is `f` again by uniqueness
(`IsSl2Triple.f_eq_of_isSl2Triple`), and both closed subgroups are reduced by Cartier's theorem.
In characteristic zero the kernel of `ad e` is the direct sum of the invariants of the triple and of
its part `𝔲` of positive weight for `ad h`, so `dim C_G(e) = dim C_G(h, e, f) + dim 𝔲`
(`IsSl2Triple.ringKrullDim_quotient_centralizerHopfIdeal_e_eq_add`).

Unlike the full centralizer `C_G(e)`, the centralizer of the triple preserves the Slodowy slice
`S = e + ker (ad f)`. Its rational points act on `S` by the adjoint action
(`TauCeti.instMulActionSlodowySlice`), and this action commutes with the contracting
action of the triple (`IsSl2Triple.basePointsRepresentation_contractingAction_apply`). Since the
adjoint action preserves every invariant polynomial function
(`TauCeti.lift_eval_basePointsRepresentation_of_mem_adjointInvariantPolynomials`), it preserves
each fibre of the adjoint quotient restricted to `S`, in particular the nilpotent fibre
`S ∩ 𝒩` (`TauCeti.nilpotentConeIdeal_le_ker_lift_eval_basePointsRepresentation_iff`).

## Main declarations

* `TauCeti.tripleCentralizerHopfIdeal`: the Hopf ideal of `C_G(h, e, f)`.
* `TauCeti.mem_quotientPointsSubgroup_tripleCentralizerHopfIdeal_iff_endOfPoint` and
  `TauCeti.mem_quotientPointsSubgroup_tripleCentralizerHopfIdeal_iff_basePointsRepresentation`:
  its algebra-valued and rational points.
* `TauCeti.tripleCentralizerHopfIdeal_eq_sup_of_lie_eq` and
  `IsSl2Triple.tripleCentralizerHopfIdeal_eq_sup`: the reductions to `C_G(e) ∩ C_G(f)` and, in
  characteristic zero, to `C_G(h) ∩ C_G(e)`.
* `TauCeti.lieSubalgebra_tripleCentralizerHopfIdeal` and
  `TauCeti.ringKrullDim_quotient_tripleCentralizerHopfIdeal`: its Lie algebra and, in
  characteristic zero, its dimension.
* `IsSl2Triple.ringKrullDim_quotient_centralizerHopfIdeal_e_eq_add`: in characteristic zero,
  `dim C_G(e) = dim C_G(h, e, f) + dim (ker (ad e) ∩ 𝔤(>0))`.
* `TauCeti.instMulActionSlodowySlice` and `TauCeti.coe_smul_slodowySlice`: the action of its
  rational points on the Slodowy slice.
* `IsSl2Triple.basePointsRepresentation_contractingAction_apply`: the centralizer of `h` commutes
  with the contracting action.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §3.7, for the centralizer of an `sl₂` triple.
* P. Slodowy, *Simple Singularities and Simple Algebraic Groups*, Lecture Notes in Mathematics
  815, Springer, 1980, §7.4, for its action on the slice.
-/

public section

open scoped TensorProduct
open WithConv

namespace TauCeti

universe u

attribute [local instance] Derivation.adjointComodule

section Basic

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Centralizers of a bracket.** The scheme-theoretic intersection `C_G(x) ∩ C_G(y)` is contained
in `C_G(⁅x, y⁆)`, because every point, with values in any commutative algebra, acts on the Lie
algebra by a Lie algebra automorphism. -/
theorem centralizerHopfIdeal_lie_le_sup (x y : 𝔤) :
    centralizerHopfIdeal H ⁅x, y⁆ ≤ centralizerHopfIdeal H x ⊔ centralizerHopfIdeal H y := by
  refine (HopfIdeal.le_iff_forall_quotientPointsSubgroup_le
    (H := _root_.CommHopfAlgCat.of k H) _ _).mpr fun A g hg ↦ ?_
  rw [CommHopfAlgCat.quotientPointsSubgroup_sup, Subgroup.mem_inf,
    mem_quotientPointsSubgroup_centralizerHopfIdeal_iff_endOfPoint,
    mem_quotientPointsSubgroup_centralizerHopfIdeal_iff_endOfPoint] at hg
  rw [mem_quotientPointsSubgroup_centralizerHopfIdeal_iff_endOfPoint, ← mul_one (1 : A),
    ← LieAlgebra.ExtendScalars.bracket_tmul,
    Derivation.endOfPoint_adjointComodule_bracket, hg.1, hg.2]

variable (H) in
/-- The Hopf ideal of the centralizer `C_G(h, e, f) = C_G(h) ∩ C_G(e) ∩ C_G(f)` of three elements
of the Lie algebra: contravariantly, the closed subgroup of points whose adjoint action fixes `h`,
`e` and `f`. For an `sl₂` triple `(h, e, f)` this is the centralizer of the triple, which acts on
the Slodowy slice `e + ker (ad f)`. -/
noncomputable def tripleCentralizerHopfIdeal (h e f : 𝔤) : HopfIdeal k H :=
  centralizerHopfIdeal H h ⊔ centralizerHopfIdeal H e ⊔ centralizerHopfIdeal H f

variable {h e f : Module.Dual k (Bialgebra.CotangentSpace k H)}

/-- The centralizer of `(h, e, f)` is the intersection of the three centralizers. -/
theorem tripleCentralizerHopfIdeal_def :
    tripleCentralizerHopfIdeal H h e f =
      centralizerHopfIdeal H h ⊔ centralizerHopfIdeal H e ⊔ centralizerHopfIdeal H f :=
  (rfl)

/-- The centralizer of `(h, e, f)` lies in the centralizer of `h`. -/
theorem centralizerHopfIdeal_le_tripleCentralizerHopfIdeal_left :
    centralizerHopfIdeal H h ≤ tripleCentralizerHopfIdeal H h e f :=
  le_sup_left.trans le_sup_left

/-- The centralizer of `(h, e, f)` lies in the centralizer of `e`. -/
theorem centralizerHopfIdeal_le_tripleCentralizerHopfIdeal_middle :
    centralizerHopfIdeal H e ≤ tripleCentralizerHopfIdeal H h e f :=
  le_sup_right.trans le_sup_left

/-- The centralizer of `(h, e, f)` lies in the centralizer of `f`. -/
theorem centralizerHopfIdeal_le_tripleCentralizerHopfIdeal_right :
    centralizerHopfIdeal H f ≤ tripleCentralizerHopfIdeal H h e f :=
  le_sup_right

/-- An algebra-valued point lies in the centralizer of `(h, e, f)` exactly when its adjoint action
fixes the constant extensions of `h`, `e` and `f`. The value algebra may be nonreduced. -/
theorem mem_quotientPointsSubgroup_tripleCentralizerHopfIdeal_iff_endOfPoint
    {A : Type*} [CommRing A] [Algebra k A] (g : WithConv (H →ₐ[k] A)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        (tripleCentralizerHopfIdeal H h e f) (CommAlgCat.of k A) ↔
      Comodule.endOfPoint 𝔤 g.ofConv (1 ⊗ₜ[k] h) = 1 ⊗ₜ[k] h ∧
        Comodule.endOfPoint 𝔤 g.ofConv (1 ⊗ₜ[k] e) = 1 ⊗ₜ[k] e ∧
          Comodule.endOfPoint 𝔤 g.ofConv (1 ⊗ₜ[k] f) = 1 ⊗ₜ[k] f := by
  rw [tripleCentralizerHopfIdeal_def, CommHopfAlgCat.quotientPointsSubgroup_sup,
    CommHopfAlgCat.quotientPointsSubgroup_sup, Subgroup.mem_inf, Subgroup.mem_inf,
    mem_quotientPointsSubgroup_centralizerHopfIdeal_iff_endOfPoint,
    mem_quotientPointsSubgroup_centralizerHopfIdeal_iff_endOfPoint,
    mem_quotientPointsSubgroup_centralizerHopfIdeal_iff_endOfPoint, and_assoc]

/-- A rational point lies in the centralizer of `(h, e, f)` exactly when its adjoint action fixes
`h`, `e` and `f`. -/
theorem mem_quotientPointsSubgroup_tripleCentralizerHopfIdeal_iff_basePointsRepresentation
    (g : WithConv (H →ₐ[k] k)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        (tripleCentralizerHopfIdeal H h e f) (CommAlgCat.of k k) ↔
      Comodule.basePointsRepresentation 𝔤 g h = h ∧
        Comodule.basePointsRepresentation 𝔤 g e = e ∧
          Comodule.basePointsRepresentation 𝔤 g f = f := by
  rw [tripleCentralizerHopfIdeal_def, CommHopfAlgCat.quotientPointsSubgroup_sup,
    CommHopfAlgCat.quotientPointsSubgroup_sup, Subgroup.mem_inf, Subgroup.mem_inf,
    mem_quotientPointsSubgroup_centralizerHopfIdeal_iff_basePointsRepresentation,
    mem_quotientPointsSubgroup_centralizerHopfIdeal_iff_basePointsRepresentation,
    mem_quotientPointsSubgroup_centralizerHopfIdeal_iff_basePointsRepresentation, and_assoc]

/-- **The centralizer of `(⁅e, f⁆, e, f)` is `C_G(e) ∩ C_G(f)`.** This holds as closed subgroup
schemes over every field. It applies to every `sl₂` triple `(h, e, f)`. -/
theorem tripleCentralizerHopfIdeal_eq_sup_of_lie_eq (hef : ⁅e, f⁆ = h) :
    tripleCentralizerHopfIdeal H h e f = centralizerHopfIdeal H e ⊔ centralizerHopfIdeal H f := by
  rw [tripleCentralizerHopfIdeal_def, sup_assoc, sup_eq_right, ← hef]
  exact centralizerHopfIdeal_lie_le_sup e f

variable (h e f) in
/-- **The Lie algebra of the centralizer of `(h, e, f)`** is the intersection of the kernels of
`ad h`, `ad e` and `ad f`. -/
theorem lieSubalgebra_tripleCentralizerHopfIdeal :
    ((tripleCentralizerHopfIdeal H h e f).lieSubalgebra (B := k)).toSubmodule =
      LinearMap.ker (LieAlgebra.ad k (Derivation k H (Bialgebra.CounitAlgebra k H k))
          (Derivation.cotangentDualLieEquiv (R := k) (H := H) h)) ⊓
        LinearMap.ker (LieAlgebra.ad k (Derivation k H (Bialgebra.CounitAlgebra k H k))
          (Derivation.cotangentDualLieEquiv (R := k) (H := H) e)) ⊓
        LinearMap.ker (LieAlgebra.ad k (Derivation k H (Bialgebra.CounitAlgebra k H k))
          (Derivation.cotangentDualLieEquiv (R := k) (H := H) f)) := by
  ext d
  simp only [Submodule.mem_inf, ← lieSubalgebra_centralizerHopfIdeal,
    LieSubalgebra.mem_toSubmodule, tripleCentralizerHopfIdeal_def,
    HopfIdeal.mem_lieSubalgebra_sup_iff]

variable (h e f) in
/-- **The dimension of the centralizer of `(h, e, f)`.** Over a field of characteristic zero it is
`dim (ker (ad h) ∩ ker (ad e) ∩ ker (ad f))`. -/
theorem ringKrullDim_quotient_tripleCentralizerHopfIdeal [CharZero k] [Algebra.FiniteType k H] :
    ringKrullDim (H ⧸ (tripleCentralizerHopfIdeal H h e f).toIdeal) =
      Module.finrank k ↥(LinearMap.ker (LieAlgebra.ad k 𝔤 h) ⊓ LinearMap.ker (LieAlgebra.ad k 𝔤 e) ⊓
        LinearMap.ker (LieAlgebra.ad k 𝔤 f)) := by
  let c := Derivation.cotangentDualLieEquiv (R := k) (H := H)
  -- Transport the kernels along the Lie algebra isomorphism `c`.
  have hmap : ((tripleCentralizerHopfIdeal H h e f).lieSubalgebra (B := k)).toSubmodule =
      (LinearMap.ker (LieAlgebra.ad k 𝔤 h) ⊓ LinearMap.ker (LieAlgebra.ad k 𝔤 e) ⊓
        LinearMap.ker (LieAlgebra.ad k 𝔤 f)).map c.toLinearEquiv.toLinearMap := by
    rw [lieSubalgebra_tripleCentralizerHopfIdeal]
    ext d
    obtain ⟨y, rfl⟩ := c.toLinearEquiv.surjective d
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
    simp only [LieEquiv.coe_toLinearEquiv, Submodule.mem_inf, LinearMap.mem_ker,
      LieAlgebra.ad_apply, ← LieEquiv.map_lie, EmbeddingLike.map_eq_zero_iff, c]
  rw [HopfIdeal.ringKrullDim_quotient_eq_finrank_lieSubalgebra,
    ← LinearEquiv.finrank_map_eq c.toLinearEquiv, ← hmap]
  -- A Lie subalgebra and its underlying submodule have the same carrier, as `k`-modules.
  rfl

/-- **The centralizer of `e` and the centralizer of the triple.** For an `sl₂` triple `(h, e, f)`
over a field of characteristic zero, `dim C_G(e) = dim C_G(h, e, f) + dim 𝔲`, where `𝔲` is the
part of `ker (ad e)` of positive weight for `ad h`. When `G` is reductive, `𝔲` is the Lie algebra of
the unipotent radical of `C_G(e)` and `C_G(h, e, f)` is a Levi factor; neither of these group-level
facts is formalized here. -/
theorem _root_.IsSl2Triple.ringKrullDim_quotient_centralizerHopfIdeal_e_eq_add [CharZero k]
    [Algebra.FiniteType k H] (t : IsSl2Triple h e f) :
    ringKrullDim (H ⧸ (centralizerHopfIdeal H e).toIdeal) =
      ringKrullDim (H ⧸ (tripleCentralizerHopfIdeal H h e f).toIdeal) +
        Module.finrank k ↥(LinearMap.ker (LieAlgebra.ad k 𝔤 e) ⊓
          ⨆ n : ℕ, (LieAlgebra.ad k 𝔤 h).eigenspace ((n + 1 : ℕ) : k)) := by
  rw [ringKrullDim_quotient_centralizerHopfIdeal, ringKrullDim_quotient_tripleCentralizerHopfIdeal]
  norm_cast
  -- `ad k 𝔤` is by definition the action `toEnd k 𝔤 𝔤` of `𝔤` on itself.
  exact t.finrank_ker_toEnd_e_eq_add (M := 𝔤)

end Basic

section CharZero

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k] {H : Type u} [CommRing H]
  [HopfAlgebra k H] [Algebra.FiniteType k H]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **The centralizer of an `sl₂` triple is the centralizer of its neutral and nilpositive
elements.** Over an algebraically closed field of characteristic zero, `C_G(h, e, f)` is
`C_G(h) ∩ C_G(e)` as closed subgroup schemes: a rational point fixing `h` and `e` carries `f` to an
element completing `(h, e)` to an `sl₂` triple, which is `f`. -/
theorem _root_.IsSl2Triple.tripleCentralizerHopfIdeal_eq_sup {h e f : 𝔤} (t : IsSl2Triple h e f) :
    tripleCentralizerHopfIdeal H h e f = centralizerHopfIdeal H h ⊔ centralizerHopfIdeal H e := by
  let G := _root_.CommHopfAlgCat.of k H
  let : IsReduced (G ⧸ (tripleCentralizerHopfIdeal H h e f).toIdeal) :=
    HopfAlgebra.isReduced_of_charZero k _
  let : IsReduced (G ⧸ (centralizerHopfIdeal H h ⊔ centralizerHopfIdeal H e).toIdeal) :=
    HopfAlgebra.isReduced_of_charZero k _
  apply HopfIdeal.eq_of_quotientPointsSubgroup_eq (H := G) (K := k)
  ext g
  rw [mem_quotientPointsSubgroup_tripleCentralizerHopfIdeal_iff_basePointsRepresentation,
    CommHopfAlgCat.quotientPointsSubgroup_sup, Subgroup.mem_inf,
    mem_quotientPointsSubgroup_centralizerHopfIdeal_iff_basePointsRepresentation,
    mem_quotientPointsSubgroup_centralizerHopfIdeal_iff_basePointsRepresentation]
  refine ⟨fun hg ↦ ⟨hg.1, hg.2.1⟩, fun ⟨hh, he⟩ ↦ ⟨hh, he, ?_⟩⟩
  have t' := t.basePointsRepresentation_adjointComodule g
  rw [hh, he] at t'
  exact (IsSl2Triple.f_eq_of_isSl2Triple k t t').symm

end CharZero

section Slice

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

variable {h e f : Module.Dual k (Bialgebra.CotangentSpace k H)}

/-- The rational points of the centralizer of `(h, e, f)` act on the Slodowy slice
`e + ker (ad f)` by the adjoint action: they fix `e` and `f`, so they preserve the slice
(`LieHom.apply_mem_slodowySlice`). -/
noncomputable instance instSMulSlodowySlice :
    SMul (CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
      (tripleCentralizerHopfIdeal H h e f) (CommAlgCat.of k k)) (slodowySlice k e f) where
  smul g x :=
    ⟨Comodule.basePointsRepresentation 𝔤 (g : WithConv (H →ₐ[k] k)) x, by
      have hg :=
        (mem_quotientPointsSubgroup_tripleCentralizerHopfIdeal_iff_basePointsRepresentation _).mp
          g.property
      simpa [hg.2.1, hg.2.2] using LieHom.apply_mem_slodowySlice
        (Derivation.basePointsAdjointLieEquiv (R := k) (H := H) g : 𝔤 →ₗ⁅k⁆ 𝔤) x.property⟩

/-- The centralizer of `(h, e, f)` acts on the Slodowy slice by the adjoint action. -/
@[simp]
theorem coe_smul_slodowySlice
    (g : CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
      (tripleCentralizerHopfIdeal H h e f) (CommAlgCat.of k k))
    (x : slodowySlice k e f) :
    ((g • x : slodowySlice k e f) : 𝔤) =
      Comodule.basePointsRepresentation 𝔤 (g : WithConv (H →ₐ[k] k)) x :=
  (rfl)

/-- **The action of the centralizer of `(h, e, f)` on the Slodowy slice.** Its rational points act
on `e + ker (ad f)` by the adjoint action. -/
noncomputable instance instMulActionSlodowySlice :
    MulAction (CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
      (tripleCentralizerHopfIdeal H h e f) (CommAlgCat.of k k)) (slodowySlice k e f) where
  one_smul x := Subtype.ext (by rw [coe_smul_slodowySlice]; simp)
  mul_smul g g' x := Subtype.ext (by
    rw [coe_smul_slodowySlice, coe_smul_slodowySlice, coe_smul_slodowySlice]
    simp)

/-- **The centralizer of `h` commutes with the contracting action** of an `sl₂` triple
`(h, e, f)`. In particular the action of the centralizer of the triple on the Slodowy slice commutes
with the contracting action. -/
theorem _root_.IsSl2Triple.basePointsRepresentation_contractingAction_apply [CharZero k]
    (t : IsSl2Triple h e f) {g : WithConv (H →ₐ[k] k)}
    (hg : g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
      (centralizerHopfIdeal H h) (CommAlgCat.of k k)) (c : kˣ) (x : 𝔤) :
    Comodule.basePointsRepresentation 𝔤 g (t.contractingAction c x) =
      t.contractingAction c (Comodule.basePointsRepresentation 𝔤 g x) := by
  rw [mem_quotientPointsSubgroup_centralizerHopfIdeal_iff_basePointsRepresentation] at hg
  simpa using LieHom.map_contractingAction
    (Derivation.basePointsAdjointLieEquiv (R := k) (H := H) g : 𝔤 →ₗ⁅k⁆ 𝔤) t t
    (by simpa using hg) c x

end Slice

end TauCeti
