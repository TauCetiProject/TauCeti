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

@[simp]
theorem harishChandraInd_obj (M : Rep.{max w u v} k L) :
    (harishChandraInd k P π).obj M = ind P.subtype (res π M) :=
  (rfl)

@[simp]
theorem harishChandraInd_map {M M' : Rep.{max w u v} k L} (f : M ⟶ M') :
    (harishChandraInd k P π).map f = indMap P.subtype ((resFunctor π).map f) :=
  (rfl)

@[simp]
theorem harishChandraRes_obj (N : Rep.{max w u v} k G) :
    (harishChandraRes k P π hπ).obj N = kerInvariants π hπ (res P.subtype N) :=
  (rfl)

@[simp]
theorem coe_harishChandraRes_map_hom_apply {N N' : Rep.{max w u v} k G} (f : N ⟶ N')
    (v : Representation.invariants ((res P.subtype N).ρ.comp π.ker.subtype)) :
    Subtype.val (((harishChandraRes k P π hπ).map f).hom v) = f.hom v :=
  (rfl)

/-- **Harish-Chandra induction is left adjoint to Harish-Chandra restriction**, for every subgroup
`P` and every commutative coefficient ring. -/
noncomputable def harishChandraIndResAdjunction :
    harishChandraInd.{w} k P π ⊣ harishChandraRes k P π hπ :=
  (resKerInvariantsAdjunction k π hπ).comp (indResAdjunction k P.subtype)

/-- The hom-set bijection of `Rep.harishChandraIndResAdjunction` is that of `Rep.indResAdjunction`
followed by that of `Rep.resKerInvariantsAdjunction`. It is not a `simp` lemma, since `simp` would
rewrite the left-hand sides of the elementwise lemmas below by it. -/
theorem harishChandraIndResAdjunction_homEquiv (M : Rep.{max w u v} k L)
    (N : Rep.{max w u v} k G) :
    (harishChandraIndResAdjunction.{w} k P π hπ).homEquiv M N =
      ((indResAdjunction.{w} k P.subtype).homEquiv (res π M) N).trans
        ((resKerInvariantsAdjunction k π hπ).homEquiv M (res P.subtype N)) :=
  congrFun (congrFun (Adjunction.comp_homEquiv _ _) M) N

/-- A morphism `R^G_{L⊂P}(M) ⟶ N` corresponds under `Rep.harishChandraIndResAdjunction` to the map
`M → N^{ker π}` sending `m` to the image of `1 ⊗ m`. -/
@[simp]
theorem coe_harishChandraIndResAdjunction_homEquiv_apply_hom_apply {M : Rep.{max w u v} k L}
    {N : Rep.{max w u v} k G} (f : (harishChandraInd k P π).obj M ⟶ N) (m : M) :
    Subtype.val (((harishChandraIndResAdjunction k P π hπ).homEquiv M N f).hom m) =
      f.hom (Representation.IndV.mk P.subtype (res π M).ρ 1 m) := by
  rw [harishChandraIndResAdjunction_homEquiv]
  exact coe_resKerInvariantsAdjunction_homEquiv_apply_hom_apply π hπ _ m

/-- A morphism `M ⟶ N^{ker π}` corresponds under `Rep.harishChandraIndResAdjunction` to the
morphism `R^G_{L⊂P}(M) ⟶ N` induced from the corresponding morphism out of the inflation of `M`. -/
@[simp]
theorem harishChandraIndResAdjunction_homEquiv_symm_apply {M : Rep.{max w u v} k L}
    {N : Rep.{max w u v} k G} (f : M ⟶ (harishChandraRes k P π hπ).obj N) :
    ((harishChandraIndResAdjunction k P π hπ).homEquiv M N).symm f =
      (indResHomEquiv P.subtype (res π M) N).symm
        ((resKerInvariantsHomEquiv π hπ M (res P.subtype N)).symm f) := by
  rw [harishChandraIndResAdjunction_homEquiv, resKerInvariantsAdjunction_homEquiv]
  simp only [indResAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  exact Equiv.symm_trans_apply _ _ f

/-- The unit of `Rep.harishChandraIndResAdjunction` sends `m : M` to `1 ⊗ m`, which is fixed by
`ker π`. It is not a `simp` lemma, since `simp` rewrites the functor objects in the type of its
left-hand side. -/
theorem coe_harishChandraIndResAdjunction_unit_app_hom_apply (M : Rep.{max w u v} k L) (m : M) :
    Subtype.val (((harishChandraIndResAdjunction k P π hπ).unit.app M).hom m) =
      Representation.IndV.mk P.subtype (res π M).ρ 1 m := by
  rw [← Adjunction.homEquiv_id]
  exact coe_harishChandraIndResAdjunction_homEquiv_apply_hom_apply k P π hπ _ m

/-- The counit of `Rep.harishChandraIndResAdjunction` is the induction of the counit of
`Rep.resKerInvariantsAdjunction`, followed by the counit of `Rep.indResAdjunction`. -/
@[simp]
theorem harishChandraIndResAdjunction_counit_app (N : Rep.{max w u v} k G) :
    (harishChandraIndResAdjunction k P π hπ).counit.app N =
      (indFunctor k P.subtype).map
          ((resKerInvariantsAdjunction k π hπ).counit.app (res P.subtype N)) ≫
        (indResAdjunction.{w} k P.subtype).counit.app N :=
  Adjunction.comp_counit_app _ _ N

section Finite

variable [P.FiniteIndex] [DecidableRel (QuotientGroup.rightRel P)] [Fintype π.ker]
  [Invertible (Fintype.card π.ker : k)]

/-- **Harish-Chandra restriction is left adjoint to Harish-Chandra induction** when `P` has finite
index in `G` and the kernel of `π` is finite of order invertible in `k`. -/
noncomputable def harishChandraResIndAdjunction :
    harishChandraRes.{w} k P π hπ ⊣ harishChandraInd k P π :=
  (resIndAdjunction k P).comp (kerInvariantsResAdjunction k π hπ)

/-- The hom-set bijection of `Rep.harishChandraResIndAdjunction` is that of
`Rep.kerInvariantsResAdjunction` followed by that of `Rep.resIndAdjunction`. It is not a `simp`
lemma, since `simp` would rewrite the left-hand sides of the elementwise lemmas below by it. -/
theorem harishChandraResIndAdjunction_homEquiv (N : Rep.{max w u v} k G)
    (M : Rep.{max w u v} k L) :
    (harishChandraResIndAdjunction.{w} k P π hπ).homEquiv N M =
      ((kerInvariantsResAdjunction k π hπ).homEquiv (res P.subtype N) M).trans
        ((resIndAdjunction.{w} k P).homEquiv N (res π M)) :=
  congrFun (congrFun (Adjunction.comp_homEquiv _ _) N) M

/-- A morphism `N^{ker π} ⟶ M` corresponds under `Rep.harishChandraResIndAdjunction` to the
morphism `N ⟶ R^G_{L⊂P}(M)` corresponding under `Rep.resIndAdjunction` to its precomposition with
the averaging projection `Rep.kerAverage`. -/
@[simp]
theorem harishChandraResIndAdjunction_homEquiv_apply {N : Rep.{max w u v} k G}
    {M : Rep.{max w u v} k L} (f : (harishChandraRes k P π hπ).obj N ⟶ M) :
    (harishChandraResIndAdjunction k P π hπ).homEquiv N M f =
      (resIndAdjunction.{w} k P).homEquiv N (res π M)
        (kerAverage π hπ (res P.subtype N) ≫ (resFunctor π).map f) := by
  rw [harishChandraResIndAdjunction_homEquiv, kerInvariantsResAdjunction_homEquiv]
  exact congrArg ((resIndAdjunction.{w} k P).homEquiv N (res π M))
    (kerInvariantsResHomEquiv_apply π hπ f)

/-- A morphism `N ⟶ R^G_{L⊂P}(M)` corresponds under `Rep.harishChandraResIndAdjunction` to the
restriction to `N^{ker π}` of the morphism corresponding to it under `Rep.resIndAdjunction`. -/
@[simp]
theorem harishChandraResIndAdjunction_homEquiv_symm_apply {N : Rep.{max w u v} k G}
    {M : Rep.{max w u v} k L} (f : N ⟶ (harishChandraInd k P π).obj M) :
    ((harishChandraResIndAdjunction k P π hπ).homEquiv N M).symm f =
      (kerInvariantsResHomEquiv π hπ (res P.subtype N) M).symm
        (((resIndAdjunction.{w} k P).homEquiv N (res π M)).symm f) := by
  rw [harishChandraResIndAdjunction_homEquiv, kerInvariantsResAdjunction_homEquiv]
  exact Equiv.symm_trans_apply _ _ f

/-- The unit of `Rep.harishChandraResIndAdjunction` is the unit of `Rep.resIndAdjunction`, followed
by the induction of the averaging projection `Rep.kerAverage`. -/
@[simp]
theorem harishChandraResIndAdjunction_unit_app (N : Rep.{max w u v} k G) :
    (harishChandraResIndAdjunction k P π hπ).unit.app N =
      (resIndAdjunction.{w} k P).unit.app N ≫
        (indFunctor k P.subtype).map (kerAverage π hπ (res P.subtype N)) := by
  rw [harishChandraResIndAdjunction, Adjunction.comp_unit_app, kerInvariantsResAdjunction_unit_app]
  -- The two sides differ only in `(resFunctor P.subtype).obj N`, which the abbreviation
  -- `Rep.res P.subtype N` unfolds to.
  rfl

/-- The counit of `Rep.harishChandraResIndAdjunction` is the counit of `Rep.resIndAdjunction`,
restricted to the `ker π`-invariants. It is not a `simp` lemma, since `simp` rewrites the functor
objects in the type of its left-hand side. -/
theorem harishChandraResIndAdjunction_counit_app_hom_apply (M : Rep.{max w u v} k L)
    (v : Representation.invariants
      ((res P.subtype (ind P.subtype (res π M))).ρ.comp π.ker.subtype)) :
    ((harishChandraResIndAdjunction k P π hπ).counit.app M).hom v =
      ((resIndAdjunction.{w} k P).counit.app (res π M)).hom (v : ind P.subtype (res π M)) := by
  have h := Adjunction.comp_counit_app (resIndAdjunction.{w} k P)
    (kerInvariantsResAdjunction k π hπ) M
  exact (congrArg (fun φ => φ.hom v) h).trans
    ((kerInvariantsResAdjunction_counit_app_hom_apply π hπ M _).trans
      (coe_kerInvariantsFunctor_map_hom_apply π hπ _ v))

end Finite

end Rep
