/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Locus.OfDim
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Stalk
import TauCeti.RingTheory.Kaehler.MapSemilinear
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

* `TauCeti.AlgebraicGeometry.nonempty_linearEquiv_kaehlerDifferential_stalk_of_mem_smoothLocusOfDim`
  and `TauCeti.AlgebraicGeometry.finrank_kaehlerDifferential_stalk_of_mem_smoothLocusOfDim`: at a
  point of `X_sm^{(d)}`, `Ω[𝒪_{X,x}⁄k] ≅ 𝒪_{X,x}^d`.
-/

public section

open CategoryTheory

universe u

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
