/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Locus.OfDim
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Stalk
public import TauCeti.RingTheory.Kaehler.MapSemilinear
import TauCeti.AlgebraicGeometry.VectorBundle.Stalk

/-!
# Differentials at the stalks of the smooth locus of dimension `d`

Let `X` be a scheme locally of finite presentation over `Spec k`. At a point `x` of the smooth
locus of dimension `d`, `X_sm^{(d)}`, the Kähler differentials `Ω[𝒪_{X,x}⁄k]` of the local ring
form a free `𝒪_{X,x}`-module of rank `d`.

On the open subscheme `V = X_sm^{(d)}` the sheaf `Ω_{V/k}` is finite locally free of rank `d`, so
its stalk at `x`, which is `Ω[𝒪_{V,x}⁄k]`, is free of rank `d`. The inclusion `V ⟶ X` is an open
immersion over `Spec k`, so it identifies the local rings `𝒪_{X,x}` and `𝒪_{V,x}` as `k`-algebras,
and the Kähler differentials with them.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.stalkMap_algebraMap`: the stalk maps of a morphism over `Spec k`
  are `k`-algebra maps;
* `AlgebraicGeometry.Scheme.Hom.stalkAlgEquivOfIsOpenImmersion`: an open immersion over `Spec k`
  identifies the local rings as `k`-algebras;
* `KaehlerDifferential.nonempty_linearEquiv_pi_of_algEquiv`: freeness of the Kähler differentials
  on a given index type passes along an isomorphism of algebras;
* `TauCeti.AlgebraicGeometry.nonempty_linearEquiv_kaehlerDifferential_stalk_of_mem_smoothLocusOfDim`
  and `TauCeti.AlgebraicGeometry.finrank_kaehlerDifferential_stalk_of_mem_smoothLocusOfDim`: at a
  point of `X_sm^{(d)}`, `Ω[𝒪_{X,x}⁄k] ≅ 𝒪_{X,x}^d`.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

noncomputable section

variable (k : Type u) [CommRing k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
  [Y.Over (Spec (.of k))]

/-- The stalk maps of a morphism over `Spec k` are compatible with the `k`-algebra structures of
the stalks. -/
theorem stalkMap_algebraMap (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (x : X) (c : k) :
    f.stalkMap x (algebraMap k (Y.presheaf.stalk (f x)) c) =
      algebraMap k (X.presheaf.stalk x) c := by
  have h : Spec.map (CommRingCat.ofHom (algebraMap k (Y.presheaf.stalk (f x))) ≫
      f.stalkMap x) = Spec.map (CommRingCat.ofHom (algebraMap k (X.presheaf.stalk x))) := by
    rw [Spec.map_comp, ← Scheme.fromSpecStalk_comp_over, ← Scheme.fromSpecStalk_comp_over,
      ← Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk, Category.assoc, comp_over]
  exact congr($(Spec.map_injective h) c)

/-- An open immersion `f : X ⟶ Y` over `Spec k` identifies the local ring of `Y` at `f x` with
the local ring of `X` at `x`, as `k`-algebras. -/
def stalkAlgEquivOfIsOpenImmersion (f : X ⟶ Y) [IsOpenImmersion f] [f.IsOver (Spec (.of k))]
    (x : X) : Y.presheaf.stalk (f x) ≃ₐ[k] X.presheaf.stalk x :=
  AlgEquiv.ofRingEquiv (f := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv)
    (stalkMap_algebraMap k f x)

/-- `stalkAlgEquivOfIsOpenImmersion` is the stalk map. -/
@[simp]
lemma stalkAlgEquivOfIsOpenImmersion_apply (f : X ⟶ Y) [IsOpenImmersion f]
    [f.IsOver (Spec (.of k))] (x : X) (a : Y.presheaf.stalk (f x)) :
    f.stalkAlgEquivOfIsOpenImmersion k x a = f.stalkMap x a :=
  (rfl)

end

end AlgebraicGeometry.Scheme.Hom

namespace KaehlerDifferential

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- If the Kähler differentials of `B` over `R` are free on an index type `ι`, so are those of an
isomorphic `R`-algebra `A`: the isomorphism of differentials along `e : A ≃ₐ[R] B` is
`e`-semilinear. -/
theorem nonempty_linearEquiv_pi_of_algEquiv {ι : Type*} (e : A ≃ₐ[R] B)
    (h : Nonempty (Ω[B⁄R] ≃ₗ[B] (ι → B))) : Nonempty (Ω[A⁄R] ≃ₗ[A] (ι → A)) := by
  obtain ⟨g⟩ := h
  refine ⟨
    { toFun ω i := e.symm (g (mapSemilinear e.toAlgHom ω) i)
      invFun v := mapSemilinear e.symm.toAlgHom (g.symm fun i ↦ e (v i))
      map_add' ω ω' := by
        ext i
        rw [map_add, map_add, Pi.add_apply, map_add, Pi.add_apply]
      map_smul' a ω := by
        ext i
        rw [mapSemilinear_smul, map_smul, Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply,
          Pi.smul_apply, smul_eq_mul]
        simp
      left_inv ω := by
        simp only [AlgEquiv.apply_symm_apply]
        exact (congrArg _ (g.symm_apply_apply _)).trans (mapSemilinear_symm_apply_apply e ω)
      right_inv v := by
        ext i
        dsimp only
        rw [mapSemilinear_apply_symm_apply]
        simp }⟩

end KaehlerDifferential

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [LocallyOfFinitePresentation (X ↘ Spec (.of k))]

/-- **The differentials at a point of the smooth locus of dimension `d` are free of rank `d`.**
At a point `x` of `X_sm^{(d)}`, `Ω[𝒪_{X,x}⁄k]` is isomorphic to `𝒪_{X,x}^d`. -/
theorem nonempty_linearEquiv_kaehlerDifferential_stalk_of_mem_smoothLocusOfDim {d : ℕ} {x : X}
    (hx : x ∈ smoothLocusOfDim k X d) :
    Nonempty (Ω[X.presheaf.stalk x⁄k] ≃ₗ[X.presheaf.stalk x] (Fin d → X.presheaf.stalk x)) := by
  let v : (smoothLocusOfDim k X d).toScheme := ⟨x, hx⟩
  -- On `V = X_sm^{(d)}`, the sheaf `Ω_{V/k}` is finite locally free of rank `d`, so its stalk at
  -- `v`, which is `Ω[𝒪_{V,v}⁄k]`, is free of rank `d`.
  let F := FiniteLocallyFreeSheaf.FixedRank.relativeDifferentials k (smoothLocusOfDim k X d) d
  have hF : F.obj.obj = (smoothLocusOfDim k X d).toScheme.relativeDifferentials k :=
    FiniteLocallyFreeSheaf.FixedRank.relativeDifferentials_obj_obj k _ d
  let b := Module.finBasisOfFinrankEq _ (F.obj.obj.presheaf.stalk v)
    ((FiniteLocallyFreeSheaf.finrank_stalk F.obj v).trans (F.rank_apply v))
  let eq : F.obj.obj.presheaf.stalk v ≃ₗ[(smoothLocusOfDim k X d).toScheme.presheaf.stalk v]
      Ω[(smoothLocusOfDim k X d).toScheme.presheaf.stalk v⁄k] := by
    rw [hF]
    exact Scheme.relativeDifferentialsStalkEquiv k _ v
  exact KaehlerDifferential.nonempty_linearEquiv_pi_of_algEquiv
    ((smoothLocusOfDim k X d).ι.stalkAlgEquivOfIsOpenImmersion k v) ⟨eq.symm.trans b.equivFun⟩

/-- At a point of the smooth locus of dimension `d`, the Kähler differentials of the local ring
form a free module. -/
theorem free_kaehlerDifferential_stalk_of_mem_smoothLocusOfDim {d : ℕ} {x : X}
    (hx : x ∈ smoothLocusOfDim k X d) :
    Module.Free (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] :=
  Module.Free.of_equiv
    (nonempty_linearEquiv_kaehlerDifferential_stalk_of_mem_smoothLocusOfDim k hx).some.symm

/-- At a point of the smooth locus of dimension `d`, the Kähler differentials of the local ring
form a finitely generated module. -/
theorem finite_kaehlerDifferential_stalk_of_mem_smoothLocusOfDim {d : ℕ} {x : X}
    (hx : x ∈ smoothLocusOfDim k X d) :
    Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] :=
  Module.Finite.equiv
    (nonempty_linearEquiv_kaehlerDifferential_stalk_of_mem_smoothLocusOfDim k hx).some.symm

/-- At a point of the smooth locus of dimension `d`, the Kähler differentials of the local ring
have rank `d`. -/
theorem finrank_kaehlerDifferential_stalk_of_mem_smoothLocusOfDim {d : ℕ} {x : X}
    (hx : x ∈ smoothLocusOfDim k X d) :
    Module.finrank (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] = d := by
  rw [(nonempty_linearEquiv_kaehlerDifferential_stalk_of_mem_smoothLocusOfDim k hx).some.finrank_eq,
    Module.finrank_fin_fun]

end TauCeti.AlgebraicGeometry
