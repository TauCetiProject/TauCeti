/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Conj
public import TauCeti.AlgebraicGeometry.Curves.StableMaps.Category

/-!
# Automorphism groups of the geometric fibres of a prestable map

Let `F` be a prestable map to a target `q : V ⟶ S`. For a geometric point `x : Spec Ω ⟶ S`, with
`Ω` an algebraically closed field, the **geometric fibre** of `F` at `x` is the base change
`F_x = F.pullback x`, a prestable map over `Spec Ω` to `V ×_S Spec Ω`. Its **abstract automorphism
group** is the group `Aut F_x` of automorphisms of its pointed source curve that commute with the
map. Stability of a prestable map is characterized by finiteness of these groups, so this file
records how they depend on the data.

* An isomorphism `F ≅ G` of prestable maps identifies the automorphism groups of their fibres.
* The fibre of a base change `F_T` at `x : Spec Ω ⟶ T` is the fibre of `F` at the composite
  `x ≫ g`, so the automorphism groups agree.
* Postcomposition with a monomorphism of targets `h : V ⟶ W`, for instance an immersion or an
  isomorphism, does not change the automorphisms of a prestable map, nor those of its fibres:
  automorphisms of the source curve that commute with `F ≫ h` commute with `F`.
* Base change along a flat surjective morphism, for instance along any extension `L / Ω` of the
  field of a geometric point, is injective on automorphisms
  (`TauCeti.AlgebraicGeometry.PrestableMap.pullbackAut_injective`). So the automorphism group of
  a geometric fibre embeds into that of the fibre at any larger algebraically closed field.

The general operations used here, `postcompAut`, `pullbackPostcompIso` and `pullbackAut_injective`,
are in `TauCeti.AlgebraicGeometry.Curves.StableMaps.Category`.

## Main definitions

In the namespace `TauCeti.AlgebraicGeometry.PrestableMap`:

* `fiberAut F x`: the abstract automorphism group of the fibre of `F` at `x : Spec Ω ⟶ S`.
* `fiberAutCongr`, `fiberAutPullback`, `fiberAutPostcomp`: the identifications of fibre
  automorphism groups along isomorphisms of prestable maps, base change, and postcomposition with
  a monomorphism of targets.
* `fiberAutBaseChange`: the homomorphism from the automorphisms of the fibre at `x` to those of
  the fibre at `Spec L ⟶ Spec Ω ⟶ S`.

## Main results

* `fiberAutCongr_apply_asIso_hom_curve`, `fiberAutPullback_apply_asIso_hom_curve`,
  `fiberAutPostcomp_apply_asIso_hom_curve`, `fiberAutBaseChange_apply_asIso_hom_curve`: the
  automorphisms of source curves produced by these identifications.
* `fiberAutBaseChange_injective`: extending the field of a point is injective on the
  automorphisms of the fibre.

## References

* K. Behrend and Yu. Manin, *Stacks of stable maps and Gromov–Witten invariants*,
  Duke Math. J. 85 (1996), 1–60, Definition 2.1 and Proposition 2.3, for the automorphisms of the
  geometric fibres of a stable map.
* W. Fulton and R. Pandharipande, *Notes on stable maps and quantum cohomology*,
  Proc. Sympos. Pure Math. 62 (1997), Part 2, 45–96, Section 1.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

namespace PrestableMap

variable {V W S T : Scheme.{u}} {q : V ⟶ S} {n : ℕ}

/-! ### Automorphism groups of fibres -/

/-- The **abstract automorphism group of the fibre** of a prestable map `F` at a point
`x : Spec Ω ⟶ S`: the automorphisms of the base change `F.pullback x`. For an algebraically closed
field `Ω` this is the automorphism group of a geometric fibre, whose finiteness characterizes
stability. -/
abbrev fiberAut (F : PrestableMap q n) {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ S) :
    Type u :=
  Aut (F.pullback x)

variable {Ω : Type u} [Field Ω]

/-- **Isomorphic prestable maps have isomorphic fibre automorphism groups.** -/
def fiberAutCongr {F G : PrestableMap q n} (e : F ≅ G) (x : Spec (.of Ω) ⟶ S) :
    F.fiberAut x ≃* G.fiberAut x :=
  ((pullbackFunctor x).mapIso e).conjAut

/-- `fiberAutCongr e x` conjugates the automorphism of the source curve of the fibre by the base
change of `e`. -/
@[simp]
theorem fiberAutCongr_apply_asIso_hom_curve {F G : PrestableMap q n} (e : F ≅ G)
    (x : Spec (.of Ω) ⟶ S) (f : F.fiberAut x) :
    (fiberAutCongr e x f).asIso.hom.curve =
      PointedPrestableFamily.pullbackMap x e.inv.curve ≫ f.asIso.hom.curve ≫
        PointedPrestableFamily.pullbackMap x e.hom.curve := by
  refine congr(($(Iso.conjAut_apply ((pullbackFunctor x).mapIso e) f)).hom.curve).trans ?_
  erw [comp_curve, comp_curve, pullbackMap_curve, pullbackMap_curve]
  -- The sides agree up to the spelling of the source curves of the base changes.
  rfl

/-- **The fibres of a base change are fibres.** The automorphism group of the fibre of the base
change `F_T` of `F` along `g : T ⟶ S` at `x : Spec Ω ⟶ T` is that of the fibre of `F` at
`x ≫ g`. -/
def fiberAutPullback (F : PrestableMap q n) (g : T ⟶ S) (x : Spec (.of Ω) ⟶ T) :
    (F.pullback g).fiberAut x ≃* F.fiberAut (x ≫ g) :=
  ((F.pullback g).pullback x).postcompAut _ (pullbackLeftPullbackSndIso_hom_snd q g x) |>.trans
    (F.pullbackCompIso g x).conjAut

/-- `fiberAutPullback g x` conjugates the automorphism of the source curve by the canonical
isomorphism `(C ×_S T) ×_T Spec Ω ≅ C ×_S Spec Ω`. -/
@[simp]
theorem fiberAutPullback_apply_asIso_hom_curve (F : PrestableMap q n) (g : T ⟶ S)
    (x : Spec (.of Ω) ⟶ T) (f : (F.pullback g).fiberAut x) :
    (F.fiberAutPullback g x f).asIso.hom.curve =
      (F.curve.pullbackCompIso g x).inv ≫ f.asIso.hom.curve ≫
        (F.curve.pullbackCompIso g x).hom := by
  simp [fiberAutPullback, Iso.conjAut_apply]
  -- The sides agree up to the spelling of the source curves of the base changes.
  rfl

/-- **Postcomposition with a monomorphism of targets does not change the fibre automorphism
groups.** For a monomorphism of targets `h : V ⟶ W` over `S`, for instance an immersion, the
automorphism group of the fibre of `F ≫ h` at `x` is that of the fibre of `F` at `x`. -/
def fiberAutPostcomp (F : PrestableMap q n) {r : W ⟶ S} (h : V ⟶ W) (hh : h ≫ r = q) [Mono h]
    (x : Spec (.of Ω) ⟶ S) :
    (F.postcomp h hh).fiberAut x ≃* F.fiberAut x :=
  -- The base change `V ×_S Spec Ω ⟶ W ×_S Spec Ω` of `h` is a monomorphism: a morphism into
  -- the fibre product is determined by its two projections, and `h` is a monomorphism.
  have : Mono (pullback.map q x r x h (𝟙 _) (𝟙 S) (by simp [hh]) (by simp)) :=
    ⟨fun a b hab ↦ pullback.hom_ext
      ((cancel_mono h).1 (by simpa using congr($hab ≫ pullback.fst r x)))
      (by simpa using congr($hab ≫ pullback.snd r x))⟩
  (F.pullbackPostcompIso h hh x).conjAut.trans ((F.pullback x).postcompAut _ _).symm

/-- `fiberAutPostcomp` keeps the automorphism of the source curve. -/
@[simp]
theorem fiberAutPostcomp_apply_asIso_hom_curve (F : PrestableMap q n) {r : W ⟶ S} (h : V ⟶ W)
    (hh : h ≫ r = q) [Mono h] (x : Spec (.of Ω) ⟶ S) (f : (F.postcomp h hh).fiberAut x) :
    (F.fiberAutPostcomp h hh x f).asIso.hom.curve = f.asIso.hom.curve := by
  simp only [fiberAutPostcomp, MulEquiv.trans_apply, postcompAut_symm_apply_asIso_hom_curve,
    Iso.conjAut_apply, Iso.trans_hom, Iso.symm_hom, comp_curve, pullbackPostcompIso_hom_curve,
    pullbackPostcompIso_inv_curve]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- Extension of the field of a point: for a field `L` with a morphism `ι : Spec L ⟶ Spec Ω`,
the homomorphism from the automorphisms of the fibre of `F` at `x : Spec Ω ⟶ S` to those of the
fibre at `ι ≫ x`, by base change along `ι`. -/
def fiberAutBaseChange (F : PrestableMap q n) (x : Spec (.of Ω) ⟶ S) {L : Type u} [Field L]
    (ι : Spec (.of L) ⟶ Spec (.of Ω)) :
    F.fiberAut x →* F.fiberAut (ι ≫ x) :=
  (F.fiberAutPullback x ι).toMonoidHom.comp ((F.pullback x).pullbackAut ι)

/-- `fiberAutBaseChange x ι` is base change of the automorphism of the source curve along `ι`,
conjugated by the canonical isomorphism `(C ×_S Spec Ω) ×_(Spec Ω) Spec L ≅ C ×_S Spec L`. -/
@[simp]
theorem fiberAutBaseChange_apply_asIso_hom_curve (F : PrestableMap q n) (x : Spec (.of Ω) ⟶ S)
    {L : Type u} [Field L] (ι : Spec (.of L) ⟶ Spec (.of Ω)) (f : F.fiberAut x) :
    (F.fiberAutBaseChange x ι f).asIso.hom.curve =
      (F.curve.pullbackCompIso x ι).inv ≫
        PointedPrestableFamily.pullbackMap ι f.asIso.hom.curve ≫
          (F.curve.pullbackCompIso x ι).hom := by
  simp [fiberAutBaseChange]
  -- The sides agree up to the spelling of the source curves of the base changes.
  rfl

/-- **Extending the field of a point is injective on fibre automorphisms.** A morphism of spectra
of fields is flat and surjective, so base change along it is injective on automorphisms. In
particular the automorphism group of a geometric fibre embeds into the automorphism group of the
geometric fibre at any larger algebraically closed field. -/
theorem fiberAutBaseChange_injective (F : PrestableMap q n) (x : Spec (.of Ω) ⟶ S) {L : Type u}
    [Field L] (ι : Spec (.of L) ⟶ Spec (.of Ω)) :
    Function.Injective (F.fiberAutBaseChange x ι) := by
  -- `Spec Ω` is a single point and `Spec L` is nonempty.
  have : Surjective ι := ⟨fun y ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  exact (F.fiberAutPullback x ι).injective.comp ((F.pullback x).pullbackAut_injective ι)

end PrestableMap

end TauCeti.AlgebraicGeometry
