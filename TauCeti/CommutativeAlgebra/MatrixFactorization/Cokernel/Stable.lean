/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Basic
public import TauCeti.CommutativeAlgebra.MatrixFactorization.BaseChange.Homotopy
public import TauCeti.CategoryTheory.Exact.Stable.Basic
public import TauCeti.Algebra.Category.FGModuleCat.Projective
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
# The stable cokernel functor of matrix factorizations

Let `X = (X₀ --d₀--> X₁ --d₁--> X₀)` be a finite-projective matrix factorization of the zero
potential. Then `d₀ ≫ d₁ = 0`, so `d₁` descends to a map `coker d₀ ⟶ X₀`
(`TauCeti.MatrixFactorization.cokernelDesc`). If a closed even map `g = d h + h d` is the
boundary of an odd map `(h₀, h₁)`, then on cokernels `g` acts as `coker d₀ ⟶ X₀ ⟶ Y₁ ⟶ coker d₀`,
the descent of `d₁`, then `h₀`, then the projection: the summand `h₁ ≫ d₀` is killed by the
projection. Since `X₀` is a finitely generated projective module, the cokernel of a
null-homotopic map factors through a projective module.

For an arbitrary potential `w : S` and a ring map `f : S →+* T` with `f w = 0`, extension of
scalars carries factorizations of `w` to factorizations of the zero potential `f w`. Composing
with the cokernel and the quotient functor to the stable category of finitely generated
`T`-modules (maps factoring through projective modules are killed) therefore descends to the
homotopy category: this is `TauCeti.MatrixFactorization.HomotopyCategory.stableCokernel`.
The hypersurface case `T = S/(w)` is
`TauCeti.MatrixFactorization.HomotopyCategory.quotientStableCokernel`, the cokernel functor from
`HMF(S,w)` to the stable category of finitely generated `S/(w)`-modules considered by Eisenbud.
Its values are the cokernels of the reductions modulo `w`.

No regularity hypothesis is used. Under Eisenbud's hypotheses (a regular local ring and a
nonzero nonunit non-zero-divisor `w`) its values are maximal Cohen–Macaulay modules and it is an
equivalence onto their stable category; neither statement is made here. The stable category of
finitely generated modules is formed with the canonical exact structure of the abelian category
`FGModuleCat T`, which requires `T` to be Noetherian.

## Main definitions

* `TauCeti.MatrixFactorization.cokernelDesc`: for the zero potential, the map
  `coker d₀ ⟶ X₀` induced by `d₁`.
* `TauCeti.MatrixFactorization.HomotopyCategory.stableCokernel`: the cokernel of the base change
  along `f`, as a functor from the matrix-factorization homotopy category to the stable category
  of finitely generated `T`-modules.
* `TauCeti.MatrixFactorization.HomotopyCategory.quotientStableCokernel`: its specialization to
  the hypersurface quotient `S/(w)`.

## Main results

* `TauCeti.MatrixFactorization.cokernelFunctor_map_hom_eq`: for the zero potential, the cokernel
  of the boundary of `(h₀, h₁)` is the descent of `d₁`, then `h₀`, then the projection.
* `TauCeti.MatrixFactorization.cokernelFunctor_map_mem_projectiveStableIdeal`: for the zero
  potential, the cokernel of a null-homotopic map factors through a projective module.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Sections 5–6.
-/

public section

noncomputable section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory Limits

variable {S T : Type u} [CommRing S] [CommRing T] {w : S}

/-! ### Cokernels of null-homotopic maps at the zero potential

The potential is only assumed to be propositionally zero, so that these results apply to the
base change of a factorization along a ring map killing its potential. -/

/-- For a factorization of a zero potential, `d₀ ≫ d₁ = 0`. -/
private theorem d₀_hom_comp_d₁_hom (hw : w = 0) (X : MatrixFactorization S w) :
    X.obj.d₀.hom ≫ X.obj.d₁.hom = 0 := by
  subst hw
  rw [← ObjectProperty.FullSubcategory.comp_hom, X.obj.d₀_comp_d₁, zero_smul,
    ObjectProperty.zero_hom]

/-- For a factorization of a zero potential, the odd-to-even differential `d₁` kills the image
of `d₀`, so it descends to a map `coker d₀ ⟶ X₀`. -/
def cokernelDesc (hw : w = 0) (X : MatrixFactorization S w) :
    cokernelFunctor.obj X ⟶ X.obj.X₀ :=
  ObjectProperty.homMk
    ((isColimitCokernelπ X).desc (CokernelCofork.ofπ X.obj.d₁.hom (d₀_hom_comp_d₁_hom hw X)))

/-- The descent of `d₁` restricts to `d₁` along the cokernel projection. -/
@[reassoc (attr := simp)]
theorem cokernelπ_cokernelDesc_hom (hw : w = 0) (X : MatrixFactorization S w) :
    cokernelπ X ≫ (cokernelDesc hw X).hom = X.obj.d₁.hom :=
  (isColimitCokernelπ X).fac _ WalkingParallelPair.one

/-- For a zero potential, the cokernel of the boundary `d h + h d` of an odd map `(h₀, h₁)` is
the descent `coker d₀ ⟶ X₀` of `d₁`, followed by `h₀ : X₀ ⟶ Y₁` and the projection
`Y₁ ⟶ coker d₀`. The summand `h₁ ≫ d₀` of the odd component is killed by the projection. -/
theorem cokernelFunctor_map_hom_eq (hw : w = 0) {X Y : MatrixFactorization S w}
    (g : X ⟶ Y) (h₀ : X.obj.X₀ ⟶ Y.obj.X₁) (h₁ : X.obj.X₁ ⟶ Y.obj.X₀)
    (hg : CurvedDuplex.nullHomotopicMap h₀ h₁ = g.hom) :
    (cokernelFunctor.map g).hom = (cokernelDesc hw X).hom ≫ h₀.hom ≫ cokernelπ Y := by
  apply (cancel_epi (cokernelπ X)).mp
  rw [cokernelπ_naturality, cokernelπ_cokernelDesc_hom_assoc, ← hg]
  simp

/-- For a zero potential, the cokernel functor sends a null-homotopic map of finite-projective
matrix factorizations to a map factoring through a projective module, namely the even component
of its source. -/
theorem cokernelFunctor_map_mem_projectiveStableIdeal [IsNoetherianRing S] (hw : w = 0)
    {X Y : MatrixFactorization S w} {g : X ⟶ Y}
    (hg : g ∈ (nullHomotopic (S := S) (w := w)).hom X Y) :
    cokernelFunctor.map g ∈
      (ExactStructure.abelian (FGModuleCat.{u} S)).projectiveStableIdeal.hom _ _ := by
  obtain ⟨h₀, h₁, hh⟩ := (mem_nullHomotopic_iff g).1 hg
  have hP : (ExactStructure.abelian (FGModuleCat.{u} S)).isProjective X.obj.X₀ :=
    (ExactStructure.abelian_isProjective_iff _).2
      (FGModuleCat.projective_of_moduleProjective S X.obj.X₀)
  have hfac : cokernelFunctor.map g =
      cokernelDesc hw X ≫ h₀ ≫ ObjectProperty.homMk (cokernelπ Y) := by
    apply ObjectProperty.hom_ext
    simpa using cokernelFunctor_map_hom_eq hw g h₀ h₁ hh
  rw [hfac, ExactStructure.mem_projectiveStableIdeal_iff]
  exact ObjectProperty.factorsThrough_comp _ hP _ _

/-- For a zero potential, the null-homotopy ideal is killed by the cokernel functor followed by
the quotient functor to the stable category of finitely generated modules. -/
theorem nullHomotopic_le_kerIdeal_cokernelFunctor_comp_projectiveStableFunctor
    [IsNoetherianRing S] (hw : w = 0) :
    nullHomotopic (S := S) (w := w) ≤
      (cokernelFunctor ⋙
        (ExactStructure.abelian (FGModuleCat.{u} S)).projectiveStableFunctor).kerIdeal := by
  intro X Y g hg
  rw [Functor.mem_kerIdeal_hom, Functor.comp_map,
    MorphismIdeal.quotientFunctor_map_eq_zero_iff]
  exact cokernelFunctor_map_mem_projectiveStableIdeal hw hg

/-! ### Descent to the homotopy category -/

namespace HomotopyCategory

/-- The **stable cokernel functor** along a ring map `f : S →+* T` killing the potential: a
finite-projective matrix factorization `X` of `w` goes to the cokernel of `T ⊗ d₀`, viewed in the
stable category of finitely generated `T`-modules. Null-homotopic maps are killed, so this is a
functor on the homotopy category `HMF(S,w)`. -/
def stableCokernel (f : S →+* T) (hw : f w = 0) [IsNoetherianRing T] :
    HomotopyCategory (S := S) (w := w) ⥤
      (ExactStructure.abelian (FGModuleCat.{u} T)).ProjectiveStableCategory :=
  (nullHomotopic (S := S) (w := w)).lift
    (baseChangeFunctor f ⋙ cokernelFunctor ⋙
      (ExactStructure.abelian (FGModuleCat.{u} T)).projectiveStableFunctor) (by
    intro X Y g hg
    rw [Functor.mem_kerIdeal_hom, Functor.comp_map]
    exact (Functor.mem_kerIdeal_hom _).1
      (MorphismIdeal.le_def.1
        (nullHomotopic_le_kerIdeal_cokernelFunctor_comp_projectiveStableFunctor hw) _
        (baseChangeFunctor_map_mem_nullHomotopic f hg)))

instance (f : S →+* T) (hw : f w = 0) [IsNoetherianRing T] :
    (stableCokernel f hw).Additive := by
  unfold stableCokernel
  infer_instance

/-- The stable cokernel functor is induced by base change followed by the cokernel. -/
theorem quotientFunctor_comp_stableCokernel (f : S →+* T) (hw : f w = 0) [IsNoetherianRing T] :
    (nullHomotopic (S := S) (w := w)).quotientFunctor ⋙ stableCokernel f hw =
      baseChangeFunctor f ⋙ cokernelFunctor ⋙
        (ExactStructure.abelian (FGModuleCat.{u} T)).projectiveStableFunctor := by
  unfold stableCokernel
  exact CategoryTheory.Quotient.lift_spec _ _ _

/-- On a representative, the stable cokernel functor takes the cokernel of the base change. -/
@[simp]
theorem stableCokernel_obj_quotientFunctor_obj (f : S →+* T) (hw : f w = 0)
    [IsNoetherianRing T] (X : MatrixFactorization S w) :
    (stableCokernel f hw).obj ((nullHomotopic (S := S) (w := w)).quotientFunctor.obj X) =
      (ExactStructure.abelian (FGModuleCat.{u} T)).projectiveStableFunctor.obj
        (cokernelFunctor.obj ((baseChangeFunctor f).obj X)) :=
  Functor.congr_obj (quotientFunctor_comp_stableCokernel f hw) X

/-- On a representative, the stable cokernel functor sends a map to the stable class of the map
induced on cokernels by its base change. -/
@[simp]
theorem stableCokernel_map_quotientFunctor_map (f : S →+* T) (hw : f w = 0)
    [IsNoetherianRing T] {X Y : MatrixFactorization S w} (g : X ⟶ Y) :
    (stableCokernel f hw).map ((nullHomotopic (S := S) (w := w)).quotientFunctor.map g) =
      eqToHom (stableCokernel_obj_quotientFunctor_obj f hw X) ≫
        (ExactStructure.abelian (FGModuleCat.{u} T)).projectiveStableFunctor.map
          (cokernelFunctor.map ((baseChangeFunctor f).map g)) ≫
        eqToHom (stableCokernel_obj_quotientFunctor_obj f hw Y).symm :=
  Functor.congr_hom (quotientFunctor_comp_stableCokernel f hw) g

/-- The stable cokernel functor of the hypersurface `S/(w)`: a finite-projective matrix
factorization of `w` goes to the cokernel of its even-to-odd differential reduced modulo `w`, in
the stable category of finitely generated modules over the hypersurface ring `S/(w)`. -/
def quotientStableCokernel [IsNoetherianRing S] :
    HomotopyCategory (S := S) (w := w) ⥤
      (ExactStructure.abelian (FGModuleCat.{u} (S ⧸ Ideal.span {w}))).ProjectiveStableCategory :=
  stableCokernel (Ideal.Quotient.mk (Ideal.span {w}))
    (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self w))

instance [IsNoetherianRing S] : (quotientStableCokernel (S := S) (w := w)).Additive := by
  unfold quotientStableCokernel
  infer_instance

/-- The hypersurface stable cokernel functor is induced by reduction modulo `w` followed by the
cokernel. -/
theorem quotientFunctor_comp_quotientStableCokernel [IsNoetherianRing S] :
    (nullHomotopic (S := S) (w := w)).quotientFunctor ⋙ quotientStableCokernel =
      baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w})) ⋙ cokernelFunctor ⋙
        (ExactStructure.abelian (FGModuleCat.{u} (S ⧸ Ideal.span {w}))).projectiveStableFunctor :=
  quotientFunctor_comp_stableCokernel _ _

end HomotopyCategory

end TauCeti.MatrixFactorization
