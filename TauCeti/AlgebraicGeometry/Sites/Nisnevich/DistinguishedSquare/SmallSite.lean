/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.MayerVietorisSquare
public import TauCeti.AlgebraicGeometry.Morphisms.Etale.Basic
public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.Affine
public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.DistinguishedSquare.Sheaf

/-!
# Elementary distinguished squares on the small Nisnevich site

Let `W` be an étale `X`-scheme and `Q` an elementary distinguished square over `W`, with
`j : U ⟶ W` and `p : V ⟶ W`. The schemes `U`, `V` and `U ×_W V` are étale over `X`, so the square
is a square in the small étale site `X.Etale`
(`TauCeti.AlgebraicGeometry.Scheme.ElementaryDistinguishedSquare.etaleSquare`). Every sheaf of sets
on the small Nisnevich site sends it to a pullback square: as on the big site
(`ElementaryDistinguishedSquare.isPullback_of_isSheaf`), this is the sheaf condition for the
covering `{j, p}` of `W`, and compatibility of a section over `V` with itself is checked on the
covering of `V ×_W V` by the diagonal and its part over `U`. Since the base change
`U ×_W V ⟶ V` of `j` is a monomorphism, the square is a Mayer–Vietoris square for the small
Nisnevich topology (`ElementaryDistinguishedSquare.mayerVietorisSquare`; Morel–Voevodsky, §3.1,
Lemma 1.6), so Mathlib's `GrothendieckTopology.MayerVietorisSquare` gives every abelian sheaf on
the small Nisnevich site a long exact Mayer–Vietoris sequence.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.ElementaryDistinguishedSquare.etaleSquare`: the square
  `U ×_W V ⟶ U, V ⟶ W` in `X.Etale`.
* `ElementaryDistinguishedSquare.ofArrows_mem_smallNisnevichTopology`: `{j, p}` covers `W` in the
  small Nisnevich topology.
* `TauCeti.AlgebraicGeometry.Scheme.ElementaryDistinguishedSquare.isPullback_of_isSheaf_small`:
  a small Nisnevich sheaf of sets sends the square to a pullback square.
* `TauCeti.AlgebraicGeometry.Scheme.ElementaryDistinguishedSquare.mayerVietorisSquare`: the square
  as a Mayer–Vietoris square of the small Nisnevich site.

## References

* F. Morel and V. Voevodsky, *𝔸¹-homotopy theory of schemes*, Publ. Math. IHÉS 90 (1999),
  §3.1, Proposition 1.4 and Lemma 1.6.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme (Etale.hom_ext Etale.comp_left)

universe v u

namespace TauCeti.AlgebraicGeometry.Scheme

namespace ElementaryDistinguishedSquare

variable {X : AlgebraicGeometry.Scheme.{u}} {W : X.Etale}
  (Q : ElementaryDistinguishedSquare W.left)

/-- The open part `U` of an elementary distinguished square over an étale `X`-scheme `W`, as an
étale `X`-scheme. -/
noncomputable abbrev etaleU : X.Etale :=
  AlgebraicGeometry.Scheme.Etale.mk (Q.j ≫ W.hom)

/-- The étale neighbourhood `V` of an elementary distinguished square over an étale `X`-scheme
`W`, as an étale `X`-scheme. -/
noncomputable abbrev etaleV : X.Etale :=
  AlgebraicGeometry.Scheme.Etale.mk (Q.p ≫ W.hom)

/-- The fibre product `U ×_W V` of an elementary distinguished square over an étale `X`-scheme
`W`, as an étale `X`-scheme. -/
noncomputable abbrev etaleUV : X.Etale :=
  AlgebraicGeometry.Scheme.Etale.mk (Limits.pullback.snd Q.j Q.p ≫ Q.p ≫ W.hom)

/-- The open immersion `j : U ⟶ W`, as a morphism of the small étale site. -/
noncomputable abbrev etaleJ : Q.etaleU ⟶ W :=
  MorphismProperty.Over.homMk Q.j

/-- The étale morphism `p : V ⟶ W`, as a morphism of the small étale site. -/
noncomputable abbrev etaleP : Q.etaleV ⟶ W :=
  MorphismProperty.Over.homMk Q.p

/-- The projection `U ×_W V ⟶ U`, as a morphism of the small étale site. -/
noncomputable abbrev etaleFst : Q.etaleUV ⟶ Q.etaleU :=
  MorphismProperty.Over.homMk (Limits.pullback.fst Q.j Q.p)
    -- The structure morphisms of `Etale.mk` objects are their defining composites.
    (show _ ≫ Q.j ≫ W.hom = _ ≫ Q.p ≫ W.hom from Limits.pullback.condition_assoc _)

/-- The projection `U ×_W V ⟶ V`, as a morphism of the small étale site. -/
noncomputable abbrev etaleSnd : Q.etaleUV ⟶ Q.etaleV :=
  MorphismProperty.Over.homMk (Limits.pullback.snd Q.j Q.p)

@[simp] lemma etaleU_hom : Q.etaleU.hom = Q.j ≫ W.hom := (rfl)
@[simp] lemma etaleV_hom : Q.etaleV.hom = Q.p ≫ W.hom := (rfl)
@[simp] lemma etaleUV_hom : Q.etaleUV.hom = Limits.pullback.snd Q.j Q.p ≫ Q.p ≫ W.hom := (rfl)
@[simp] lemma etaleJ_left : Q.etaleJ.left = Q.j := (rfl)
@[simp] lemma etaleP_left : Q.etaleP.left = Q.p := (rfl)
@[simp] lemma etaleFst_left : Q.etaleFst.left = Limits.pullback.fst Q.j Q.p := (rfl)
@[simp] lemma etaleSnd_left : Q.etaleSnd.left = Limits.pullback.snd Q.j Q.p := (rfl)

/-- The square `U ×_W V ⟶ U, V ⟶ W` of an elementary distinguished square over `W`, in the small
étale site of `X`. -/
@[expose, simps]
noncomputable def etaleSquare : Square X.Etale where
  f₁₂ := Q.etaleFst
  f₁₃ := Q.etaleSnd
  f₂₄ := Q.etaleJ
  f₃₄ := Q.etaleP
  -- The underlying scheme morphisms of `homMk` arrows are the given ones.
  fac := Etale.hom_ext (show _ ≫ Q.j = _ ≫ Q.p from Limits.pullback.condition)

instance mono_etaleSnd : Mono Q.etaleSnd where
  right_cancellation a b h := Etale.hom_ext <|
    (cancel_mono (Limits.pullback.snd Q.j Q.p) (g := a.left) (h := b.left)).1
      (congrArg (fun f ↦ f.left) h)

instance mono_etaleSquare_f₁₃ : Mono Q.etaleSquare.f₁₃ :=
  Q.mono_etaleSnd

/-- The morphisms `j` and `p` in the small étale site, indexed by `Bool`
(`true ↦ j`, `false ↦ p`). -/
noncomputable abbrev etaleArrows :
    ∀ b : Bool, (Bool.rec Q.etaleV Q.etaleU b : X.Etale) ⟶ W :=
  Bool.rec (motive := fun b ↦ (Bool.rec Q.etaleV Q.etaleU b : X.Etale) ⟶ W) Q.etaleP Q.etaleJ

/-- `{j, p}` covers `W` in the small Nisnevich topology. -/
theorem ofArrows_mem_smallNisnevichTopology :
    Sieve.ofArrows _ Q.etaleArrows ∈ X.smallNisnevichTopology W := by
  rw [AlgebraicGeometry.Scheme.ofArrows_mem_smallNisnevichTopology_iff]
  refine ⟨fun b ↦ by cases b <;> dsimp <;> infer_instance, fun s ↦ ?_⟩
  obtain ⟨b, x, hx, hiso⟩ := Q.isNisnevichCovering.exists_isIso s
  cases b
  · exact ⟨false, x, hx, hiso⟩
  · exact ⟨true, x, hx, hiso⟩

/-- For a morphism `g : T ⟶ V ×_W V` from an étale `X`-scheme, the pullback along `g` of the
diagonal (`true`) or of the part of `V ×_W V` over `U` (`false`), as an étale `X`-scheme. -/
private noncomputable abbrev diagonalCoverObj {T : X.Etale}
    (g : T.left ⟶ Limits.pullback Q.p Q.p) (c : Bool) : X.Etale :=
  AlgebraicGeometry.Scheme.Etale.mk (Limits.pullback.fst g (Q.diagonalArrows c) ≫ T.hom)

/-- The open immersion of `diagonalCoverObj g c` into `T`. -/
private noncomputable abbrev diagonalCoverHom {T : X.Etale}
    (g : T.left ⟶ Limits.pullback Q.p Q.p) (c : Bool) : Q.diagonalCoverObj g c ⟶ T :=
  MorphismProperty.Over.homMk (Limits.pullback.fst g (Q.diagonalArrows c))

/-- The pullbacks along `g : T ⟶ V ×_W V` of the diagonal and of the part over `U` cover `T` in
the small Nisnevich topology. -/
private theorem ofArrows_diagonalCoverHom_mem {T : X.Etale} (g : T.left ⟶ Limits.pullback Q.p Q.p) :
    Sieve.ofArrows _ (Q.diagonalCoverHom g) ∈ X.smallNisnevichTopology T := by
  rw [AlgebraicGeometry.Scheme.ofArrows_mem_smallNisnevichTopology_iff]
  exact Q.isNisnevichCovering_diagonal.pullback g

variable {F : X.Etaleᵒᵖ ⥤ Type v}

/-- If a section `a` over `U` and a section `b` over `V` agree on `U ×_W V`, then their pullbacks
along morphisms `T ⟶ U` and `T ⟶ V` that agree over `W` are equal. -/
theorem map_eq_map_of_comp_eq {a : F.obj (op Q.etaleU)} {b : F.obj (op Q.etaleV)}
    (hab : F.map Q.etaleFst.op a = F.map Q.etaleSnd.op b) {T : X.Etale} (gu : T ⟶ Q.etaleU)
    (gv : T ⟶ Q.etaleV) (h : gu ≫ Q.etaleJ = gv ≫ Q.etaleP) :
    F.map gu.op a = F.map gv.op b := by
  have hl : gu.left ≫ Q.j = gv.left ≫ Q.p := by simpa using congrArg (fun f ↦ f.left) h
  have hv : gv.left ≫ Q.p ≫ W.hom = T.hom := MorphismProperty.Over.w gv
  have hw : Limits.pullback.lift gu.left gv.left hl ≫ Limits.pullback.snd Q.j Q.p ≫ Q.p ≫ W.hom =
      T.hom :=
    (Limits.pullback.lift_snd_assoc _ _ _ _).trans hv
  set l : T ⟶ Q.etaleUV := MorphismProperty.Over.homMk (Limits.pullback.lift gu.left gv.left hl) hw
  have h₁ : gu = l ≫ Q.etaleFst := Etale.hom_ext (Limits.pullback.lift_fst _ _ hl).symm
  have h₂ : gv = l ≫ Q.etaleSnd := Etale.hom_ext (Limits.pullback.lift_snd _ _ hl).symm
  rw [h₁, h₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hab]

variable (hF : Presieve.IsSheaf X.smallNisnevichTopology F)
include hF

/-- A sheaf on the small Nisnevich site is separated for the covering `{j, p}`. -/
theorem ext_of_isSheaf_small {s t : F.obj (op W)}
    (hj : F.map Q.etaleJ.op s = F.map Q.etaleJ.op t)
    (hp : F.map Q.etaleP.op s = F.map Q.etaleP.op t) : s = t := by
  refine ((Presieve.isSheafFor_iff_generate _).2
    (hF _ Q.ofArrows_mem_smallNisnevichTopology)).isSeparatedFor.ext ?_
  rintro _ _ ⟨b⟩
  cases b
  · exact hp
  · exact hj

/-- A section `b` over `V` of a sheaf on the small Nisnevich site that agrees on `U ×_W V` with a
section over `U` has equal pullbacks along any two morphisms `T ⟶ V` that agree over `W`. -/
private theorem map_eq_map_of_isSheaf_small {a : F.obj (op Q.etaleU)} {b : F.obj (op Q.etaleV)}
    (hab : F.map Q.etaleFst.op a = F.map Q.etaleSnd.op b) {T : X.Etale} (b₁ b₂ : T ⟶ Q.etaleV)
    (h : b₁ ≫ Q.etaleP = b₂ ≫ Q.etaleP) : F.map b₁.op b = F.map b₂.op b := by
  have hw : b₁.left ≫ Q.p = b₂.left ≫ Q.p := by simpa using congrArg (fun f ↦ f.left) h
  set g := Limits.pullback.lift b₁.left b₂.left hw
  refine ((Presieve.isSheafFor_iff_generate _).2
    (hF _ (Q.ofArrows_diagonalCoverHom_mem g))).isSeparatedFor.ext ?_
  rintro _ _ ⟨c⟩
  simp only [← Functor.map_comp_apply, ← op_comp]
  -- On the pullback of `Q.diagonalArrows c`, `b₁` and `b₂` restrict to the two projections.
  have hg (c : Bool) {bπ : T ⟶ Q.etaleV} {π : Limits.pullback Q.p Q.p ⟶ Q.V}
      (hπ : g ≫ π = bπ.left) : (Q.diagonalCoverHom g c).left ≫ bπ.left =
        Limits.pullback.snd g (Q.diagonalArrows c) ≫ Q.diagonalArrows c ≫ π :=
    (congrArg (Limits.pullback.fst g (Q.diagonalArrows c) ≫ ·) hπ).symm.trans
      (Limits.pullback.condition_assoc _)
  have hb₁ : b₁.left ≫ Q.p ≫ W.hom = T.hom := MorphismProperty.Over.w b₁
  cases c
  · -- Over `U`, both composites agree with a section pulled back from `U`.
    set m := Limits.pullback.snd g (Q.diagonalArrows false) ≫
      Limits.pullback.snd (Limits.pullback.fst Q.p Q.p ≫ Q.p) Q.j
    have hm : m ≫ Q.j = (Q.diagonalCoverHom g false).left ≫ b₁.left ≫ Q.p := by
      have h₁ : m ≫ Q.j = Limits.pullback.snd g (Q.diagonalArrows false) ≫
          Q.diagonalArrows false ≫ Limits.pullback.fst Q.p Q.p ≫ Q.p := by
        simp only [m, Category.assoc]
        rw [← Limits.pullback.condition (f := Limits.pullback.fst Q.p Q.p ≫ Q.p) (g := Q.j)]
      exact h₁.trans ((hg false (Limits.pullback.lift_fst _ _ hw) =≫ Q.p).symm.trans
        (Category.assoc _ _ _))
    -- `simp` and `rw` do not see through the `X.Etale` comma structure here, so the remaining
    -- equalities of scheme morphisms are assembled from `hm`, `hb₁` and `hπ` by reassociation.
    have hmw : m ≫ Q.j ≫ W.hom = (Q.diagonalCoverObj g false).hom :=
      (Category.assoc _ _ _).symm.trans ((hm =≫ W.hom).trans
        ((Category.assoc _ _ _).trans ((Q.diagonalCoverHom g false).left ≫=
          ((Category.assoc _ _ _).trans hb₁))))
    set n : Q.diagonalCoverObj g false ⟶ Q.etaleU := MorphismProperty.Over.homMk m hmw
    have e (π : T ⟶ Q.etaleV) (hπ : π.left ≫ Q.p = b₁.left ≫ Q.p) :
        F.map (Q.diagonalCoverHom g false ≫ π).op b = F.map n.op a :=
      (Q.map_eq_map_of_comp_eq hab _ _ (Etale.hom_ext (hm.trans
        (((Q.diagonalCoverHom g false).left ≫= hπ.symm).trans (Category.assoc _ _ _).symm)))).symm
    rw [e b₁ rfl, e b₂ hw.symm]
  · -- On the diagonal, both composites agree: `Q.diagonalArrows true` is the diagonal of `p`.
    have : Q.diagonalCoverHom g true ≫ b₁ = Q.diagonalCoverHom g true ≫ b₂ :=
      Etale.hom_ext ((hg true (Limits.pullback.lift_fst _ _ hw)).trans
        ((Limits.pullback.snd g (Q.diagonalArrows true) ≫= (Limits.pullback.diagonal_fst Q.p).trans
          (Limits.pullback.diagonal_snd Q.p).symm).trans
            (hg true (Limits.pullback.lift_snd _ _ hw)).symm))
    rw [this]

/-- **Small Nisnevich sheaves on elementary distinguished squares** (Morel–Voevodsky, §3.1,
the only-if direction of Proposition 1.4): a sheaf of sets on the small Nisnevich site of `X`
sends an elementary distinguished square over an étale `X`-scheme `W` to a pullback square, so
`F(W) → F(U) ×_{F(U ×_W V)} F(V)` is bijective. -/
theorem isPullback_of_isSheaf_small :
    IsPullback (F.map Q.etaleJ.op) (F.map Q.etaleP.op) (F.map Q.etaleFst.op)
      (F.map Q.etaleSnd.op) := by
  rw [Types.isPullback_iff]
  refine ⟨?_, fun s t ⟨hj, hp⟩ ↦ Q.ext_of_isSheaf_small hF hj hp, fun a b hab ↦ ?_⟩
  · rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp]
    exact congrArg (fun f ↦ F.map f.op) Q.etaleSquare.fac
  · have hsheaf : (Presieve.ofArrows _ Q.etaleArrows).IsSheafFor F :=
      (Presieve.isSheafFor_iff_generate _).2 (hF _ Q.ofArrows_mem_smallNisnevichTopology)
    rw [Presieve.isSheafFor_arrows_iff] at hsheaf
    obtain ⟨t, ht, -⟩ := hsheaf (fun c ↦ Bool.rec b a c) (by
      intro c d Z gc gd h
      cases c <;> cases d
      · exact Q.map_eq_map_of_isSheaf_small hF hab gc gd h
      · exact (Q.map_eq_map_of_comp_eq hab gd gc h.symm).symm
      · exact Q.map_eq_map_of_comp_eq hab gc gd h
      · -- `j` is a monomorphism.
        obtain rfl : gc = gd := Etale.hom_ext <|
          (cancel_mono Q.j (g := gc.left) (h := gd.left)).1 (congrArg (fun f ↦ f.left) h)
        rfl)
    exact ⟨t, ht true, ht false⟩

omit hF in
/-- **Elementary distinguished squares are Mayer–Vietoris squares** of the small Nisnevich site
(Morel–Voevodsky, §3.1, Lemma 1.6): the square `U ×_W V ⟶ U, V ⟶ W` becomes a pushout square in
sheaves of sets, so every abelian sheaf on the small Nisnevich site has a long exact
Mayer–Vietoris sequence for it. -/
@[expose, simps! toSquare]
noncomputable def mayerVietorisSquare : X.smallNisnevichTopology.MayerVietorisSquare :=
  -- `(Q.etaleSquare.op.map F.obj).IsPullback` unfolds, through the projections of
  -- `etaleSquare`, to the statement of `isPullback_of_isSheaf_small`.
  GrothendieckTopology.MayerVietorisSquare.mk' Q.etaleSquare fun F ↦
    Q.isPullback_of_isSheaf_small ((isSheaf_iff_isSheaf_of_type _ _).1 F.property)

end ElementaryDistinguishedSquare

end TauCeti.AlgebraicGeometry.Scheme
