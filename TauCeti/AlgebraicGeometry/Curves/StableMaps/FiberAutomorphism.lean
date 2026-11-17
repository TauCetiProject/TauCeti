/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
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
  field of a geometric point, is injective on automorphisms, because the projection of source
  curves is then an epimorphism of schemes. So the automorphism group of a geometric fibre embeds
  into that of the fibre at any larger algebraically closed field.

## Main definitions

In the namespace `TauCeti.AlgebraicGeometry.PrestableMap`:

* `postcompAut`: for a monomorphism of targets `h`, the identification
  `Aut F ≃* Aut (F ≫ h)`.
* `fiberAut F x`: the abstract automorphism group of the fibre of `F` at `x : Spec Ω ⟶ S`.
* `fiberAutCongr`, `fiberAutPullback`, `fiberAutPostcomp`: the identifications of fibre
  automorphism groups along isomorphisms of prestable maps, base change, and postcomposition with
  a monomorphism of targets.
* `fiberAutBaseChange`: the homomorphism from the automorphisms of the fibre at `x` to those of
  the fibre at `Spec L ⟶ Spec Ω ⟶ S`.

## Main results

* `pullbackAut_injective`: base change along a flat surjective morphism is injective on
  automorphisms.
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

/-! ### Postcomposition with a monomorphism of targets -/

/-- For a monomorphism of targets `h : V ⟶ W` over `S`, the automorphisms of a prestable map `F`
are those of its postcomposition `F ≫ h`: an automorphism of the source curve commutes with
`F ≫ h` exactly when it commutes with `F`. -/
def postcompAut (F : PrestableMap q n) {r : W ⟶ S} (h : V ⟶ W) (hh : h ≫ r = q) [Mono h] :
    Aut F ≃* Aut (F.postcomp h hh) :=
  (Functor.FullyFaithful.ofFullyFaithful
    (postcompFunctor (n := n) h hh)).autMulEquivOfFullyFaithful F

/-- `postcompAut` keeps the automorphism of the source curve. -/
@[simp]
theorem postcompAut_apply_asIso_hom_curve (F : PrestableMap q n) {r : W ⟶ S} (h : V ⟶ W)
    (hh : h ≫ r = q) [Mono h] (e : Aut F) :
    (F.postcompAut h hh e).asIso.hom.curve = e.asIso.hom.curve :=
  (rfl)

/-- Base change commutes with postcomposition: the base change along `x : T ⟶ S` of `F ≫ h` is
the base change of `F`, postcomposed with the base change `V ×_S T ⟶ W ×_S T` of `h`. The two
have the same source curve. -/
def pullbackPostcompIso (F : PrestableMap q n) {r : W ⟶ S} (h : V ⟶ W) (hh : h ≫ r = q)
    (x : T ⟶ S) :
    (F.postcomp h hh).pullback x ≅
      (F.pullback x).postcomp (pullback.map q x r x h (𝟙 T) (𝟙 S) (by simp [hh]) (by simp))
        (by simp) :=
  isoMk (Iso.refl _) (by
    dsimp only [postcomp, pullback, PointedPrestableFamily.pullback]
    apply pullback.hom_ext <;> simp)

/-- `pullbackPostcompIso` is the identity on source curves. -/
@[simp]
theorem pullbackPostcompIso_hom_curve (F : PrestableMap q n) {r : W ⟶ S} (h : V ⟶ W)
    (hh : h ≫ r = q) (x : T ⟶ S) :
    (F.pullbackPostcompIso h hh x).hom.curve = 𝟙 _ := by
  rw [pullbackPostcompIso]
  exact isoMk_hom_curve _ _

/-! ### Base change along a flat surjective morphism -/

/-- **Base change along a flat surjective morphism is injective on automorphisms.** The
projection `C ×_S T ⟶ C` of source curves is then flat and surjective, hence an epimorphism of
schemes, and an automorphism of `F` is determined by its composite with it. -/
theorem pullbackAut_injective (F : PrestableMap q n) (g : T ⟶ S) [Flat g] [Surjective g] :
    Function.Injective (F.pullbackAut g) := by
  have := Flat.epi_of_flat_of_surjective (pullback.fst F.curve.toBase g)
  intro e e' hee'
  refine Aut.ext (Iso.ext (hom_ext (PointedPrestableFamily.hom_ext ?_)))
  rw [← cancel_epi (pullback.fst F.curve.toBase g),
    (PointedPrestableFamily.isPullback_pullbackMap_hom g e.asIso.hom.curve).w,
    (PointedPrestableFamily.isPullback_pullbackMap_hom g e'.asIso.hom.curve).w]
  have := congr(($hee').asIso.hom.curve.hom ≫ pullback.fst F.curve.toBase g)
  simp only [pullbackAut_apply_asIso_hom, pullbackMap_curve] at this
  exact this

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

/-- **The fibres of a base change are fibres.** The automorphism group of the fibre of the base
change `F_T` of `F` along `g : T ⟶ S` at `x : Spec Ω ⟶ T` is that of the fibre of `F` at
`x ≫ g`. -/
def fiberAutPullback (F : PrestableMap q n) (g : T ⟶ S) (x : Spec (.of Ω) ⟶ T) :
    (F.pullback g).fiberAut x ≃* F.fiberAut (x ≫ g) :=
  ((F.pullback g).pullback x).postcompAut _ (pullbackLeftPullbackSndIso_hom_snd q g x) |>.trans
    (F.pullbackCompIso g x).conjAut

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

/-- Extension of the field of a point: for a field `L` with a morphism `ι : Spec L ⟶ Spec Ω`,
the homomorphism from the automorphisms of the fibre of `F` at `x : Spec Ω ⟶ S` to those of the
fibre at `ι ≫ x`, by base change along `ι`. -/
def fiberAutBaseChange (F : PrestableMap q n) (x : Spec (.of Ω) ⟶ S) {L : Type u} [Field L]
    (ι : Spec (.of L) ⟶ Spec (.of Ω)) :
    F.fiberAut x →* F.fiberAut (ι ≫ x) :=
  (F.fiberAutPullback x ι).toMonoidHom.comp ((F.pullback x).pullbackAut ι)

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
