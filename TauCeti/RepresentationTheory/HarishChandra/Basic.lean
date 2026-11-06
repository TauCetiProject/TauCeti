/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.FiniteIndex
public import TauCeti.RepresentationTheory.Inflation

/-!
# Harish-Chandra induction and restriction

Let `P` be a subgroup of a group `G` and let `π : P →* L` be a surjective homomorphism with
kernel `U`. The motivating case is a parabolic subgroup `P = L ⋉ U` of a finite reductive group,
with `π` the projection onto its Levi factor `L`. For any commutative coefficient ring `k`:

* **Harish-Chandra induction** `R^G_{L⊂P}` inflates a representation of `L` to `P` along `π`
  and induces it to `G`:
  `R^G_{L⊂P}(M) = Ind_P^G (Inf_L^P M)`;
* **Harish-Chandra restriction** `*R^G_{L⊂P}` restricts a representation of `G` to `P` and takes
  `U`-invariants, on which `L ≃* P ⧸ U` acts: `*R^G_{L⊂P}(N) = N^U`.

Inflation is restriction along `π`, Mathlib's `Rep.resFunctor π`, and induction is Mathlib's
`Rep.indFunctor`, so `R^G_{L⊂P}(M)` is the module `k[G] ⊗_{k[P]} M`. This file proves that the
two functors are adjoint on both sides:

* `R^G_{L⊂P} ⊣ *R^G_{L⊂P}` for every subgroup `P` and every coefficient ring, composing
  Frobenius reciprocity `Ind ⊣ Res` with the adjunction between inflation and invariants;
* `*R^G_{L⊂P} ⊣ R^G_{L⊂P}` when `P` has finite index and `U` is finite of order invertible in `k`,
  composing `Res ⊣ Ind` for finite index with the averaging adjunction between invariants and
  inflation.

For a finite reductive group in characteristic `p`, the unipotent radical `U` is a `p`-group, so
the second adjunction applies whenever `p` is invertible in `k`.

## Main definitions

* `Rep.harishChandraInd k P π`: Harish-Chandra induction `Rep k L ⥤ Rep k G`.
* `Rep.harishChandraRes k P π hπ`: Harish-Chandra restriction `Rep k G ⥤ Rep k L`.
* `Rep.harishChandraIndResAdjunction k P π hπ`: `R^G_{L⊂P} ⊣ *R^G_{L⊂P}`.
* `Rep.harishChandraResIndAdjunction k P π hπ`: `*R^G_{L⊂P} ⊣ R^G_{L⊂P}`, for `P` of finite index
  and `ker π` finite of invertible order.

## References

* O. Dudas and J. Michel, *Lectures on finite reductive groups and their representations*
  (2015), §7.
* R. B. Howlett and G. I. Lehrer, *On Harish-Chandra induction and restriction for modules of
  Levi subgroups*, J. Algebra **165** (1994), 172–183.
* F. Digne and J. Michel, *Representations of Finite Groups of Lie Type*, 2nd ed. (2020).
-/

public section

open CategoryTheory

universe w u v v'

namespace Rep

variable (k : Type u) [CommRing k] {G : Type v} [Group G] (P : Subgroup G)
  {L : Type v'} [Group L] (π : P →* L) (hπ : Function.Surjective π)

/-- **Harish-Chandra induction** `R^G_{L⊂P}`: a representation of `L` is inflated to `P` along
`π : P →* L` and induced from `P` to `G`.

The body is exposed so that `(harishChandraInd k P π).obj M` unfolds to the induced
representation `Rep.ind P.subtype (Rep.res π M)`. -/
@[expose]
noncomputable def harishChandraInd : Rep.{max w u v} k L ⥤ Rep.{max w u v} k G :=
  resFunctor π ⋙ indFunctor k P.subtype

/-- **Harish-Chandra restriction** `*R^G_{L⊂P}`: a representation of `G` is restricted to `P`, and
`L` acts on its `ker π`-invariants through `P ⧸ ker π ≃* L`.

The body is exposed so that `(harishChandraRes k P π hπ).obj N` unfolds to the submodule
`Rep.kerInvariants π hπ (Rep.res P.subtype N)` of `N`. -/
@[expose]
noncomputable def harishChandraRes : Rep.{max w u v} k G ⥤ Rep.{max w u v} k L :=
  resFunctor P.subtype ⋙ kerInvariantsFunctor k π hπ

theorem harishChandraInd_obj (M : Rep.{max w u v} k L) :
    (harishChandraInd k P π).obj M = ind P.subtype (res π M) :=
  rfl

theorem harishChandraRes_obj (N : Rep.{max w u v} k G) :
    (harishChandraRes k P π hπ).obj N = kerInvariants π hπ (res P.subtype N) :=
  rfl

/-- **Harish-Chandra induction is left adjoint to Harish-Chandra restriction**, for every subgroup
`P` and every commutative coefficient ring. -/
noncomputable def harishChandraIndResAdjunction :
    harishChandraInd.{w} k P π ⊣ harishChandraRes k P π hπ :=
  (resKerInvariantsAdjunction k π hπ).comp (indResAdjunction k P.subtype)

/-- A morphism `R^G_{L⊂P}(M) ⟶ N` corresponds under `Rep.harishChandraIndResAdjunction` to the map
`M → N^{ker π}` sending `m` to the image of `1 ⊗ m`. -/
@[simp]
theorem coe_harishChandraIndResAdjunction_homEquiv_apply_hom_apply {M : Rep.{max w u v} k L}
    {N : Rep.{max w u v} k G} (f : (harishChandraInd k P π).obj M ⟶ N) (m : M) :
    Subtype.val (((harishChandraIndResAdjunction k P π hπ).homEquiv M N f).hom m) =
      f.hom (Representation.IndV.mk P.subtype (res π M).ρ 1 m) := by
  have h := congrFun (congrFun (Adjunction.comp_homEquiv (resKerInvariantsAdjunction k π hπ)
    (indResAdjunction k P.subtype)) M) N
  exact (congrArg (fun e => Subtype.val ((e f).hom m)) h).trans
    (coe_resKerInvariantsAdjunction_homEquiv_apply_hom_apply π hπ _ m)

section Finite

variable [P.FiniteIndex] [DecidableRel (QuotientGroup.rightRel P)] [Fintype π.ker]
  [Invertible (Fintype.card π.ker : k)]

/-- **Harish-Chandra restriction is left adjoint to Harish-Chandra induction** when `P` has finite
index in `G` and the kernel of `π` is finite of order invertible in `k`. -/
noncomputable def harishChandraResIndAdjunction :
    harishChandraRes.{w} k P π hπ ⊣ harishChandraInd k P π :=
  (resIndAdjunction k P).comp (kerInvariantsResAdjunction k π hπ)

end Finite

end Rep
