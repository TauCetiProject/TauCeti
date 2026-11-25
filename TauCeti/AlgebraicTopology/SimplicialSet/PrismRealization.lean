/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.TopCat.ToSSet
public import TauCeti.AlgebraicTopology.SimplicialSet.ProdStdSimplex.Realization
public import TauCeti.AlgebraicTopology.SimplicialSet.TrivialFibration
public import TauCeti.AlgebraicTopology.SimplicialSet.WeakEquivalence

/-!
# Geometric realization of simplicial homotopies

A homotopy of simplicial sets `H : X ⊗ Δ[1] ⟶ Y` from `f` to `g` realizes to a homotopy from `|f|`
to `|g|` (`SSet.Homotopy.toTop`). Consequently simplicial homotopy equivalences, and in particular
the trivial fibrations of the Kan–Quillen model structure (the maps with the right lifting property
with respect to all monomorphisms), are weak equivalences
(`SSet.modelCategoryQuillen.weakEquivalence_of_homotopyEquiv`,
`SSet.modelCategoryQuillen.weakEquivalence_of_rlp_monomorphisms`). This is the converse direction
to Mathlib's `TopCat.Homotopy.toSSet`. Together, the two directions show that two maps from `X` to
the singular simplicial set of a space `T` are simplicially homotopic exactly when their adjoint
maps `|X| ⟶ T` are homotopic (`SSet.nonempty_homotopy_iff_homotopic_homEquiv_symm`).

To realize a simplicial homotopy we construct the continuous map
`SSet.toTopCylinder X : |X| × I → |X ⊗ Δ[1]|` restricting to `|ι₀|` and `|ι₁|` on the two ends.
It is adjoint to a map from `X` to the singular simplicial set of the path space
`C(I, |X ⊗ Δ[1]|)`, obtained over each simplex of `X` from the prism triangulation
`SSet.prodStdSimplex₁.prism`, the `q = 1` specialization of `SSet.prodStdSimplex.triangulate`
along `Convexity.StdSimplex.homeomorphI.symm`.

## Main declarations

* `SSet.prodStdSimplex₁.prism`: the triangulation `Δᵖ × I → |Δ[p] ⊗ Δ[1]|` of the prism, natural
  in `Δ[p]` (`SSet.prodStdSimplex₁.prism_naturality`), with ends `ι₀` and `ι₁`.
* `SSet.toTopCylinder X`: the triangulation `|X| × I → |X ⊗ Δ[1]|` of the realized cylinder,
  natural in `X` (`SSet.toTopCylinder_naturality`).
* `SSet.Homotopy.toTop`: the realization of a simplicial homotopy.
* `SSet.toTopHomotopyEquiv`: the realization of a simplicial homotopy equivalence.
* `SSet.nonempty_homotopy_iff_homotopic_homEquiv_symm`: maps into a singular simplicial set are
  homotopic exactly when their adjoints are.

## References

* J. Milnor, *The geometric realization of a semi-simplicial complex*, Ann. of Math. 65 (1957),
  357–362.
* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Sections I.2 and I.11.
-/

public section

open CategoryTheory MonoidalCategory Opposite Convexity Simplicial MorphismProperty
  HomotopicalAlgebra

universe u

namespace SSet

variable {X Y : SSet.{u}}

namespace prodStdSimplex₁

/-! ### The prism -/

open unitInterval

variable {p : ℕ}

variable (p) in
/-- The triangulation of the prism `Δᵖ × I` into the geometric realization `|Δ[p] ⊗ Δ[1]|`,
obtained from `SSet.prodStdSimplex.triangulate p 1` along `StdSimplex.homeomorphI.symm`. -/
noncomputable def prism : C(StdSimplex ℝ (Fin (p + 1)) × I, |(Δ[p] ⊗ Δ[1] : SSet.{u})|) :=
  (prodStdSimplex.triangulate p 1).comp
    ((ContinuousMap.id _).prodMap (StdSimplex.homeomorphI.symm : C(I, StdSimplex ℝ (Fin 2))))

/-- Pointwise formula for `SSet.prodStdSimplex₁.prism` in terms of
`SSet.prodStdSimplex.triangulate`. -/
lemma prism_apply (s : StdSimplex ℝ (Fin (p + 1))) (t : I) :
    prism.{u} p (s, t) =
      prodStdSimplex.triangulate p 1 (s, StdSimplex.homeomorphI.symm t) :=
  (rfl)

/-- The triangulation of the prism is natural in the simplex. -/
lemma prism_naturality {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (s : StdSimplex ℝ (Fin (m + 1))) (t : I) :
    toTop.map (SSet.stdSimplex.map f ▷ Δ[1]) (prism.{u} m (s, t)) =
      prism n (StdSimplex.map f s, t) := by
  simpa [prism_apply, StdSimplex.map_id] using
    prodStdSimplex.triangulate_naturality f (𝟙 ⦋1⦌) s (StdSimplex.homeomorphI.symm t)

private lemma prism_of_eq {t : I} {b : Fin 2} (ht : StdSimplex.homeomorphI.symm t = .single b)
    (ι : Δ[p] ⟶ Δ[p] ⊗ Δ[1])
    (hι₁ : (ι.app (op ⦋p⦌) (stdSimplex.objEquiv.symm (𝟙 ⦋p⦌))).1 =
      stdSimplex.objEquiv.symm (𝟙 ⦋p⦌))
    (hι₂ : ⇑(stdSimplex.objEquiv (ι.app (op ⦋p⦌) (stdSimplex.objEquiv.symm (𝟙 ⦋p⦌))).2) =
      fun _ ↦ b)
    (s : StdSimplex ℝ (Fin (p + 1))) :
    prism.{u} p (s, t) = toTop.map ι (toTopObjMk (stdSimplex.objEquiv.symm (𝟙 ⦋p⦌)) s) := by
  rw [toTop_map_toTopObjMk,
    ← prodStdSimplex.triangulate_map_objEquiv (ι.app (op ⦋p⦌) (stdSimplex.objEquiv.symm (𝟙 ⦋p⦌))) s,
    hι₁, Equiv.apply_symm_apply, hι₂]
  simp [prism_apply, ht, StdSimplex.map_id, StdSimplex.map_const]

/-- The bottom face `t = 0` of the triangulation of the prism is the bottom inclusion `ι₀`. -/
@[simp]
lemma prism_zero (s : StdSimplex ℝ (Fin (p + 1))) :
    prism.{u} p (s, 0) = toTop.map ι₀ (toTopObjMk (stdSimplex.objEquiv.symm (𝟙 ⦋p⦌)) s) :=
  -- Levelwise, `ι₀` pairs the identity first component with the constant vertex `0` in `Δ[1]`.
  prism_of_eq StdSimplex.homeomorphI_symm_zero ι₀ rfl (funext fun _ ↦ rfl) s

/-- The top face `t = 1` of the triangulation of the prism is the top inclusion `ι₁`. -/
@[simp]
lemma prism_one (s : StdSimplex ℝ (Fin (p + 1))) :
    prism.{u} p (s, 1) = toTop.map ι₁ (toTopObjMk (stdSimplex.objEquiv.symm (𝟙 ⦋p⦌)) s) :=
  -- Levelwise, `ι₁` pairs the identity first component with the constant vertex `1` in `Δ[1]`.
  prism_of_eq StdSimplex.homeomorphI_symm_one ι₁ rfl (funext fun _ ↦ rfl) s

end prodStdSimplex₁

/-! ### Realization of the cylinder and of homotopies -/

open unitInterval

variable (X) in
/-- The map from `X` to the singular simplicial set of the path space `C(I, |X ⊗ Δ[1]|)` sending
an `n`-simplex `x` to the triangulated prism over it, the composite of
`SSet.prodStdSimplex₁.prism n` with the realization of `x ▷ Δ[1]`. -/
private noncomputable def cylinderPaths :
    X ⟶ TopCat.toSSet.obj (TopCat.of C(I, |X ⊗ Δ[1]|)) where
  app n := ↾fun x ↦ (TopCat.toSSetObjEquiv _ n).symm
    (((toTop.map (yonedaEquiv.symm x ▷ Δ[1])).hom.comp (prodStdSimplex₁.prism _)).curry)
  naturality n m f := by
    ext x
    induction n using Opposite.rec with | op n
    induction m using Opposite.rec with | op m
    induction n using SimplexCategory.rec with | _ n
    induction m using SimplexCategory.rec with | _ m
    obtain ⟨f, rfl⟩ : ∃ g : ⦋m⦌ ⟶ ⦋n⦌, g.op = f := ⟨f.unop, rfl⟩
    apply (TopCat.toSSetObjEquiv _ _).injective
    ext w t
    simp only [TypeCat.Fun.toFun_apply, ConcreteCategory.comp_apply, TypeCat.ofHom_apply,
      Equiv.apply_symm_apply, ContinuousMap.curry_apply, ContinuousMap.comp_apply]
    rw [← yonedaEquiv_symm_naturality_left, MonoidalCategory.comp_whiskerRight, Functor.map_comp,
      TopCat.hom_comp, ContinuousMap.comp_apply, prodStdSimplex₁.prism_naturality,
      TopCat.toSSetObjEquiv_naturality_apply, Equiv.apply_symm_apply, ContinuousMap.curry_apply,
      ContinuousMap.comp_apply]

/-- The `ι₀` and `ι₁` simplices of the prism over a simplex `x` of `X` are mapped by `x ▷ Δ[1]` to
the `ι₀` and `ι₁` simplices of `X ⊗ Δ[1]` over `x`. -/
private lemma whiskerRight_app_app_objEquiv_symm_id {n : ℕ} (x : X _⦋n⦌) (i : Δ[n] ⟶ Δ[n] ⊗ Δ[1])
    (j : X ⟶ X ⊗ Δ[1]) (hij : i ≫ yonedaEquiv.symm x ▷ Δ[1] = yonedaEquiv.symm x ≫ j) :
    (yonedaEquiv.symm x ▷ Δ[1]).app _ (i.app _ (stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))) =
      j.app _ x := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, hij, NatTrans.comp_app,
    ConcreteCategory.comp_apply, yonedaEquiv_symm_app_objEquiv_symm, op_id,
    CategoryTheory.Functor.map_id, types_id_apply]

variable (X) in
/-- The triangulation of the realization of the cylinder `X ⊗ Δ[1]`: the continuous map
`|X| × I → |X ⊗ Δ[1]|` which over the realization of each simplex `x` of `X` is the triangulation
`SSet.prodStdSimplex₁.prism` of the prism over `x`. -/
noncomputable def toTopCylinder : C(|X| × I, |X ⊗ Δ[1]|) :=
  ((sSetTopAdj.homEquiv _ _).symm (cylinderPaths X)).hom.uncurry

/-- Over the realization of a simplex, the triangulation of the realized cylinder is the
triangulation of the prism. -/
lemma toTopCylinder_toTopObjMk {n : ℕ} (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) (t : I) :
    toTopCylinder X (toTopObjMk x w, t) =
      toTop.map (yonedaEquiv.symm x ▷ Δ[1]) (prodStdSimplex₁.prism n (w, t)) := by
  have h := apply_toTopObjMk ((sSetTopAdj.homEquiv _ _).symm (cylinderPaths X)) x w
  rw [Equiv.apply_symm_apply] at h
  exact DFunLike.congr_fun h t

/-- `SSet.toTopCylinder` is natural in the simplicial set `X`. -/
theorem toTopCylinder_naturality (f : X ⟶ Y) (z : |X|) (t : I) :
    toTopCylinder Y (toTop.map f z, t) = toTop.map (f ▷ Δ[1]) (toTopCylinder X (z, t)) := by
  refine ConcreteCategory.congr_hom (toTop_hom_ext
    (g₁ := TopCat.ofHom ⟨fun z ↦ toTopCylinder Y (toTop.map f z, t), by fun_prop⟩)
    (g₂ := TopCat.ofHom ⟨fun z ↦ toTop.map (f ▷ Δ[1]) (toTopCylinder X (z, t)), by fun_prop⟩)
    fun n x w ↦ ?_) z
  simp only [TopCat.hom_ofHom, ContinuousMap.coe_mk, toTop_map_toTopObjMk,
    toTopCylinder_toTopObjMk]
  have hf : yonedaEquiv.symm (f.app (op ⦋n⦌) x) = yonedaEquiv.symm x ≫ f :=
    yonedaEquiv.injective (by simp [yonedaEquiv_comp])
  rw [hf, MonoidalCategory.comp_whiskerRight, Functor.map_comp, ConcreteCategory.comp_apply]

/-- If at the end `t` the triangulation of every prism is the realization of `j`, for a natural
family `j : Z ⟶ Z ⊗ Δ[1]`, then so is the triangulation of the realized cylinder. -/
private lemma toTopCylinder_of_prism {t : I} (j : ∀ {Z : SSet.{u}}, Z ⟶ Z ⊗ Δ[1])
    (hj : ∀ {Z Z' : SSet.{u}} (f : Z ⟶ Z'), j ≫ f ▷ Δ[1] = f ≫ j)
    (hprism : ∀ (n : ℕ) (s : StdSimplex ℝ (Fin (n + 1))), prodStdSimplex₁.prism n (s, t) =
      toTop.map j (toTopObjMk (stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)) s))
    (z : |X|) : toTopCylinder X (z, t) = toTop.map j z := by
  refine ConcreteCategory.congr_hom (toTop_hom_ext (g₁ := TopCat.ofHom
    ((toTopCylinder X).comp ⟨fun z ↦ (z, t), by fun_prop⟩)) fun n x w ↦ ?_) z
  refine (TopCat.ofHom_apply _ _).trans ?_
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [toTopCylinder_toTopObjMk, hprism, toTop_map_toTopObjMk, toTop_map_toTopObjMk,
    toTop_map_toTopObjMk, whiskerRight_app_app_objEquiv_symm_id x j j (hj _)]

/-- The bottom of the triangulation of the realized cylinder is the realization of `ι₀`. -/
@[simp]
lemma toTopCylinder_zero (z : |X|) : toTopCylinder X (z, 0) = toTop.map ι₀ z :=
  toTopCylinder_of_prism ι₀ ι₀_comp (fun _ ↦ prodStdSimplex₁.prism_zero) z

/-- The top of the triangulation of the realized cylinder is the realization of `ι₁`. -/
@[simp]
lemma toTopCylinder_one (z : |X|) : toTopCylinder X (z, 1) = toTop.map ι₁ z :=
  toTopCylinder_of_prism ι₁ ι₁_comp (fun _ ↦ prodStdSimplex₁.prism_one) z

/-- The realization of a simplicial homotopy `H` between `f` and `g`: the homotopy between `|f|` and
`|g|` given by the realization of `H.h : X ⊗ Δ[1] ⟶ Y` composed with the triangulation of the
realized cylinder. -/
noncomputable def Homotopy.toTop {f g : X ⟶ Y} (H : Homotopy f g) :
    TopCat.Homotopy (SSet.toTop.map f) (SSet.toTop.map g) where
  -- Inside this declaration `toTop` would refer to `SSet.Homotopy.toTop` itself.
  toFun z := SSet.toTop.map H.h (toTopCylinder X (z.2, z.1))
  continuous_toFun := by fun_prop
  map_zero_left z := by
    rw [toTopCylinder_zero, ← ConcreteCategory.comp_apply, ← Functor.map_comp, H.h₀]
  map_one_left z := by
    rw [toTopCylinder_one, ← ConcreteCategory.comp_apply, ← Functor.map_comp, H.h₁]

/-- The realization of a simplicial homotopy at time `t` is the realization of the homotopy
applied to the triangulation of the realized cylinder. -/
@[simp]
lemma Homotopy.toTop_apply {f g : X ⟶ Y} (H : Homotopy f g) (t : I) (z : |X|) :
    H.toTop (t, z) = SSet.toTop.map H.h (toTopCylinder X (z, t)) :=
  (rfl)

/-- Two maps from `X` to the singular simplicial set of a space `T` are simplicially homotopic
exactly when their adjoint maps `|X| ⟶ T` are homotopic. -/
theorem nonempty_homotopy_iff_homotopic_homEquiv_symm {T : TopCat.{u}}
    (φ ψ : X ⟶ TopCat.toSSet.obj T) :
    Nonempty (Homotopy φ ψ) ↔
      ((sSetTopAdj.homEquiv X T).symm φ).hom.Homotopic ((sSetTopAdj.homEquiv X T).symm ψ).hom := by
  refine ⟨fun ⟨H⟩ ↦ ?_, fun ⟨H⟩ ↦ ?_⟩
  · rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
    exact ⟨(TopCat.Homotopy.refl (sSetTopAdj.counit.app T)).comp H.toTop⟩
  · have e (χ : X ⟶ TopCat.toSSet.obj T) :
        sSetTopAdj.unit.app X ≫ TopCat.toSSet.map ((sSetTopAdj.homEquiv X T).symm χ) = χ :=
      (sSetTopAdj.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
    have H' := (TopCat.Homotopy.toSSet (f := (sSetTopAdj.homEquiv X T).symm φ)
      (g := (sSetTopAdj.homEquiv X T).symm ψ) H).precomp (sSetTopAdj.unit.app X)
    rw [e, e] at H'
    exact ⟨H'⟩

/-- The realization of a simplicial homotopy equivalence is a homotopy equivalence. -/
noncomputable def toTopHomotopyEquiv (f : X ⟶ Y) (g : Y ⟶ X) (H₁ : Homotopy (f ≫ g) (𝟙 X))
    (H₂ : Homotopy (g ≫ f) (𝟙 Y)) : ContinuousMap.HomotopyEquiv |X| |Y| where
  toFun := (toTop.map f).hom
  invFun := (toTop.map g).hom
  left_inv := by
    have := H₁.toTop
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at this
    exact ⟨this⟩
  right_inv := by
    have := H₂.toTop
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at this
    exact ⟨this⟩

/-- The realization of a simplicial homotopy equivalence has underlying map `|f|`. -/
@[simp]
lemma toTopHomotopyEquiv_toFun (f : X ⟶ Y) (g : Y ⟶ X) (H₁ : Homotopy (f ≫ g) (𝟙 X))
    (H₂ : Homotopy (g ≫ f) (𝟙 Y)) : (toTopHomotopyEquiv f g H₁ H₂).toFun = (toTop.map f).hom :=
  (rfl)

/-- The realization of a simplicial homotopy equivalence has homotopy inverse `|g|`. -/
@[simp]
lemma toTopHomotopyEquiv_invFun (f : X ⟶ Y) (g : Y ⟶ X) (H₁ : Homotopy (f ≫ g) (𝟙 X))
    (H₂ : Homotopy (g ≫ f) (𝟙 Y)) : (toTopHomotopyEquiv f g H₁ H₂).invFun = (toTop.map g).hom :=
  (rfl)

namespace modelCategoryQuillen

/-- A simplicial homotopy equivalence is a weak equivalence. -/
theorem weakEquivalence_of_homotopyEquiv (f : X ⟶ Y) (g : Y ⟶ X) (H₁ : Homotopy (f ≫ g) (𝟙 X))
    (H₂ : Homotopy (g ≫ f) (𝟙 Y)) : WeakEquivalence f :=
  (weakEquivalence_iff f).2 (toTopHomotopyEquiv f g H₁ H₂).isWeakHomotopyEquivalence

/-- A morphism with the right lifting property with respect to all monomorphisms, that is, a
trivial fibration of the Kan–Quillen model structure, is a weak equivalence. -/
theorem weakEquivalence_of_rlp_monomorphisms {p : X ⟶ Y} (hp : (monomorphisms SSet.{u}).rlp p) :
    WeakEquivalence p := by
  have := isSplitEpi_of_rlp_monomorphisms hp
  let h := Shrinking.ofRLP hp (section_ p) (IsSplitEpi.id p)
  exact weakEquivalence_of_homotopyEquiv p h.section_ h.homotopy
    (RelativeMorphism.Homotopy.ofEq (congrArg _ h.section_comp))

end modelCategoryQuillen

end SSet
