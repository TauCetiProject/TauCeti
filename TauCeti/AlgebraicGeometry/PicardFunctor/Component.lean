/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.PicardFunctor.PicZero.BaseChange
public import TauCeti.AlgebraicGeometry.PicardFunctor.PicZero.FieldPoint

/-!
# The degree-`d` components of the relative Picard presheaf

Let `f : X ⟶ S` be a morphism of schemes. For an integer `d`, the **degree-`d` subfunctor**
`Pic^d_{X/S}` of the relative Picard presheaf `T ↦ Pic(X_T) / Pic(T)` consists, at a scheme `T`
over `S`, of the classes whose fibre degree (`relativePicardFiberDegree`) is `d` at every
geometric point `Spec Ω ⟶ T` (`relativePicardDegreeSubfunctor`). In degree zero it is the
degree-zero subfunctor `Pic⁰_{X/S}` (`relativePicardDegreeSubfunctor_zero`). Over a scheme `T`
with a point, the subfunctors of different degrees have disjoint sections
(`disjoint_relativePicardDegreeSubfunctor_obj`).

For a smooth proper geometrically connected family of curves, the fibre degree is additive, so
products, inverses and powers of classes add, negate and multiply degrees
(`mul_mem_relativePicardDegreeSubfunctor_obj` and its companions). Consequently the group
`Pic⁰_{X/S}(T)` acts on `Pic^d_{X/S}(T)` by multiplication. The action is pretransitive, and free
and transitive whenever `Pic^d_{X/S}(T)` is nonempty: for any section `c` of `Pic^d_{X/S}(T)`,
`z ↦ z • c` is a bijection `relativePicardDegreeZeroSubgroup f T ≃ Pic^d_{X/S}(T)`
(`relativePicardDegreeSubfunctorObjEquiv`). The set `Pic^d_{X/S}(T)` may be empty, so
`Pic^d_{X/S}` is a pseudo-torsor under `Pic⁰_{X/S}`, before representability. A section `c₀`
of `Pic^d_{X/S}` over `S` itself, for instance the class of a line bundle on `X` of degree `d`
on every fibre, trivializes it: translation by the pullbacks of `c₀` is a natural isomorphism
`Pic⁰_{X/S} ≅ Pic^d_{X/S}` (`relativePicardDegreeZeroIsoDegree`).

At a field-valued point `Spec L ⟶ S`, for `f` quasi-compact and quasi-separated, a section lies
in `Pic^d_{X/S}` exactly when its line-bundle class on `X_L` has degree `d` over `L`
(`mem_relativePicardDegreeSubfunctor_obj_iff_eulerDegree_eq`). So these sections are the
classes of line bundles of degree `d` on `X_L`. They need not exhaust the `L`-points of the
degree-`d` part of the fppf Picard sheaf: for a curve over a field `k` without a rational point,
a `k`-rational divisor class need not come from a line bundle on `X`, the obstruction lying in
the Brauer group of `k`. The Picard sheaf is not treated here. The base change comparison of
relative Picard presheaves identifies `Pic^d` of a base change with the restriction of
`Pic^d_{X/S}` (`relativePicardDegreeSubfunctorBaseChangeIso`).

Sheafification, representability by an open and closed subscheme of a Picard scheme, and the
local constancy of the degree are not treated here.

## Main declarations

* `TauCeti.AlgebraicGeometry.relativePicardDegreeSubfunctor`: the subfunctor `Pic^d_{X/S}`;
* `TauCeti.AlgebraicGeometry.disjoint_relativePicardDegreeSubfunctor_obj`: different degrees
  are disjoint over a nonempty scheme;
* `TauCeti.AlgebraicGeometry.mul_mem_relativePicardDegreeSubfunctor_obj`: degrees add under
  products of classes, for a family of curves;
* `TauCeti.AlgebraicGeometry.relativePicardDegreeSubfunctorObjEquiv`: a section of
  `Pic^d_{X/S}(T)` identifies it with `Pic⁰_{X/S}(T)` by translation, so `Pic^d_{X/S}(T)` is a
  principal homogeneous set under `Pic⁰_{X/S}(T)` when it is nonempty;
* `TauCeti.AlgebraicGeometry.relativePicardDegreeZeroIsoDegree`: a section of degree `d` over
  `S` trivializes `Pic^d_{X/S}` as a translate of `Pic⁰_{X/S}`;
* `TauCeti.AlgebraicGeometry.mem_relativePicardDegreeSubfunctor_obj_iff_eulerDegree_eq`:
  `Pic^d_{X/S}` at a field-valued point;
* `TauCeti.AlgebraicGeometry.relativePicardDegreeSubfunctorBaseChangeIso`: base change of
  `Pic^d_{X/S}`.

## References

* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Sections 9.2 and 9.5 (the components `Pic^d` and `Pic⁰`).
* B. Poonen, M. Stoll, *The Cassels–Tate pairing on polarized abelian varieties*, Ann. of Math.
  150 (1999), Section 2 (the torsors `Pic^d` under `Pic⁰` of a curve without a rational point).
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- **The degree-`d` subfunctor `Pic^d_{X/S}`** of the relative Picard presheaf
`T ↦ Pic(X_T) / Pic(T)` of `f : X ⟶ S`: at a scheme `T` over `S`, the classes whose fibre degree
is `d` at every geometric point `Spec Ω ⟶ T`, with `Ω` algebraically closed. It is a subfunctor
by naturality of the fibre degree (`relativePicardFiberDegree_map`).

As for `relativePicardDegreeZeroSubfunctor`, which is its degree-zero case
(`relativePicardDegreeSubfunctor_zero`), this is `Pic^d_{X/S}` for families of curves; for other
`f` the condition inherits the junk values of `LineBundleClass.eulerDegree`. -/
def relativePicardDegreeSubfunctor (d : ℤ) :
    Subfunctor (relativePicardPresheaf f ⋙ forget CommGrpCat) where
  obj T := {c | ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (ξ : Spec (.of Ω) ⟶ T.unop.left),
    relativePicardFiberDegree f ξ c = d}
  map {T T'} φ c hc Ω _ _ ξ' := by
    rw [← hc Ω (ξ' ≫ φ.unop.left)]
    exact relativePicardFiberDegree_map f φ ξ' c

/-- A section of `T ↦ Pic(X_T) / Pic(T)` lies in `Pic^d_{X/S}` exactly when its fibre degree is
`d` at every geometric point of `T`. -/
@[simp]
lemma mem_relativePicardDegreeSubfunctor_obj_iff {d : ℤ} {T : (Over S)ᵒᵖ}
    {c : (relativePicardPresheaf f).obj T} :
    c ∈ (relativePicardDegreeSubfunctor f d).obj T ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (ξ : Spec (.of Ω) ⟶ T.unop.left),
        relativePicardFiberDegree f ξ c = d :=
  Iff.rfl

/-- The degree-zero component `Pic^0_{X/S}` is the degree-zero subfunctor `Pic⁰_{X/S}`. -/
@[simp]
lemma relativePicardDegreeSubfunctor_zero :
    relativePicardDegreeSubfunctor f 0 = relativePicardDegreeZeroSubfunctor f := by
  ext T c
  exact (mem_relativePicardDegreeSubfunctor_obj_iff f).trans
    (mem_relativePicardDegreeZeroSubfunctor_obj_iff f).symm

/-- **Components of different degrees are disjoint** over a scheme `T` with a point: the fibre
degree at a geometric point over it determines the degree. -/
theorem disjoint_relativePicardDegreeSubfunctor_obj {d e : ℤ} (h : d ≠ e) {T : (Over S)ᵒᵖ}
    [Nonempty T.unop.left] :
    Disjoint ((relativePicardDegreeSubfunctor f d).obj T)
      ((relativePicardDegreeSubfunctor f e).obj T) := by
  rw [Set.disjoint_left]
  intro c hd he
  obtain ⟨x⟩ := ‹Nonempty T.unop.left›
  -- A geometric point over `x`: the algebraic closure of its residue field.
  let ξ : Spec (.of (AlgebraicClosure (T.unop.left.residueField x))) ⟶ T.unop.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (T.unop.left.residueField x)
      (AlgebraicClosure (T.unop.left.residueField x)))) ≫ T.unop.left.fromSpecResidueField x
  exact h ((hd _ ξ).symm.trans (he _ ξ))

section Smooth

variable [IsProper f] [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f]

/-- For a smooth proper geometrically connected family of curves, the product of classes of
degrees `d` and `e` has degree `d + e`. -/
lemma mul_mem_relativePicardDegreeSubfunctor_obj {d e : ℤ} {T : (Over S)ᵒᵖ}
    {c c' : (relativePicardPresheaf f).obj T} (hc : c ∈ (relativePicardDegreeSubfunctor f d).obj T)
    (hc' : c' ∈ (relativePicardDegreeSubfunctor f e).obj T) :
    c * c' ∈ (relativePicardDegreeSubfunctor f (d + e)).obj T := fun Ω _ _ ξ ↦ by
  rw [relativePicardFiberDegree_mul_of_smooth, hc Ω ξ, hc' Ω ξ]

/-- For a smooth proper geometrically connected family of curves, the inverse of a class of
degree `d` has degree `-d`. -/
lemma inv_mem_relativePicardDegreeSubfunctor_obj {d : ℤ} {T : (Over S)ᵒᵖ}
    {c : (relativePicardPresheaf f).obj T} (hc : c ∈ (relativePicardDegreeSubfunctor f d).obj T) :
    c⁻¹ ∈ (relativePicardDegreeSubfunctor f (-d)).obj T := fun Ω _ _ ξ ↦ by
  rw [relativePicardFiberDegree_inv_of_smooth, hc Ω ξ]

/-- For a smooth proper geometrically connected family of curves, the quotient of a class of
degree `d` by a class of degree `e` has degree `d - e`. -/
lemma div_mem_relativePicardDegreeSubfunctor_obj {d e : ℤ} {T : (Over S)ᵒᵖ}
    {c c' : (relativePicardPresheaf f).obj T} (hc : c ∈ (relativePicardDegreeSubfunctor f d).obj T)
    (hc' : c' ∈ (relativePicardDegreeSubfunctor f e).obj T) :
    c / c' ∈ (relativePicardDegreeSubfunctor f (d - e)).obj T := by
  rw [div_eq_mul_inv, sub_eq_add_neg]
  exact mul_mem_relativePicardDegreeSubfunctor_obj f hc
    (inv_mem_relativePicardDegreeSubfunctor_obj f hc')

/-- For a smooth proper geometrically connected family of curves, the `n`-th power of a class of
degree `d` has degree `n * d`. -/
lemma zpow_mem_relativePicardDegreeSubfunctor_obj {d : ℤ} {T : (Over S)ᵒᵖ}
    {c : (relativePicardPresheaf f).obj T} (hc : c ∈ (relativePicardDegreeSubfunctor f d).obj T)
    (n : ℤ) : c ^ n ∈ (relativePicardDegreeSubfunctor f (n * d)).obj T := fun Ω _ _ ξ ↦ by
  rw [relativePicardFiberDegree_zpow_of_smooth, hc Ω ξ]

/-- For a smooth proper geometrically connected family of curves and a class `c` of degree `d`,
a class `c'` has degree `e` exactly when `c' * c` has degree `e + d`. -/
lemma mul_mem_relativePicardDegreeSubfunctor_obj_iff {d e : ℤ} {T : (Over S)ᵒᵖ}
    {c c' : (relativePicardPresheaf f).obj T}
    (hc : c ∈ (relativePicardDegreeSubfunctor f d).obj T) :
    c' * c ∈ (relativePicardDegreeSubfunctor f (e + d)).obj T ↔
      c' ∈ (relativePicardDegreeSubfunctor f e).obj T := by
  refine ⟨fun h Ω _ _ ξ ↦ ?_, fun h ↦ mul_mem_relativePicardDegreeSubfunctor_obj f h hc⟩
  have h' := h Ω ξ
  rw [relativePicardFiberDegree_mul_of_smooth, hc Ω ξ] at h'
  omega

/-- For a smooth proper geometrically connected family of curves, the quotient of two classes of
the same degree lies in `Pic⁰_{X/S}`. -/
lemma div_mem_relativePicardDegreeZeroSubgroup {d : ℤ} {T : (Over S)ᵒᵖ}
    {c c' : (relativePicardPresheaf f).obj T} (hc : c ∈ (relativePicardDegreeSubfunctor f d).obj T)
    (hc' : c' ∈ (relativePicardDegreeSubfunctor f d).obj T) :
    c' / c ∈ relativePicardDegreeZeroSubgroup f T := by
  rw [mem_relativePicardDegreeZeroSubgroup_iff, ← relativePicardDegreeSubfunctor_zero, ← sub_self d]
  exact div_mem_relativePicardDegreeSubfunctor_obj f hc' hc

/-- For a smooth proper geometrically connected family of curves, multiplying a class of degree
`d` by a class of `Pic⁰_{X/S}` gives a class of degree `d`. -/
lemma mul_mem_relativePicardDegreeSubfunctor_obj_of_mem_relativePicardDegreeZeroSubgroup
    {d : ℤ} {T : (Over S)ᵒᵖ} {z c : (relativePicardPresheaf f).obj T}
    (hz : z ∈ relativePicardDegreeZeroSubgroup f T)
    (hc : c ∈ (relativePicardDegreeSubfunctor f d).obj T) :
    z * c ∈ (relativePicardDegreeSubfunctor f d).obj T := by
  rw [mem_relativePicardDegreeZeroSubgroup_iff, ← relativePicardDegreeSubfunctor_zero] at hz
  simpa using mul_mem_relativePicardDegreeSubfunctor_obj f hz hc

-- The sections of a subfunctor of `relativePicardPresheaf f ⋙ forget CommGrpCat` are typed in the
-- composite functor, which does not unfold to the group `(relativePicardPresheaf f).obj T` at
-- instance transparency, so the components below name their values in that group.

/-- **`Pic⁰_{X/S}(T)` acts on `Pic^d_{X/S}(T)`** by multiplication of classes, for a smooth proper
geometrically connected family of curves. -/
instance (d : ℤ) (T : (Over S)ᵒᵖ) :
    MulAction (relativePicardDegreeZeroSubgroup f T) ((relativePicardDegreeSubfunctor f d).obj T)
    where
  smul z c :=
    let a : (relativePicardPresheaf f).obj T := c.val
    ⟨(z : (relativePicardPresheaf f).obj T) * a,
      mul_mem_relativePicardDegreeSubfunctor_obj_of_mem_relativePicardDegreeZeroSubgroup f
        z.property c.property⟩
  one_smul c :=
    let a : (relativePicardPresheaf f).obj T := c.val
    Subtype.ext (one_mul a)
  mul_smul z w c :=
    let a : (relativePicardPresheaf f).obj T := c.val
    Subtype.ext (mul_assoc (z : (relativePicardPresheaf f).obj T) w a)

/-- The action of `Pic⁰_{X/S}(T)` on `Pic^d_{X/S}(T)` is multiplication of classes. -/
@[simp]
lemma coe_relativePicardDegreeZeroSubgroup_smul {d : ℤ} {T : (Over S)ᵒᵖ}
    (z : relativePicardDegreeZeroSubgroup f T) {c : (relativePicardPresheaf f).obj T}
    (hc : c ∈ (relativePicardDegreeSubfunctor f d).obj T) :
    (z • (⟨c, hc⟩ : (relativePicardDegreeSubfunctor f d).obj T)).val =
      (z : (relativePicardPresheaf f).obj T) * c :=
  (rfl)

/-- **A section of `Pic^d_{X/S}(T)` identifies it with `Pic⁰_{X/S}(T)`**, for a smooth proper
geometrically connected family of curves: for a section `c` of degree `d`, translation
`z ↦ z • c` is a bijection from `Pic⁰_{X/S}(T)` onto `Pic^d_{X/S}(T)`. So `Pic^d_{X/S}(T)` is a
principal homogeneous set under `Pic⁰_{X/S}(T)` when it is nonempty; it may be empty. -/
def relativePicardDegreeSubfunctorObjEquiv {d : ℤ} {T : (Over S)ᵒᵖ}
    (c : (relativePicardDegreeSubfunctor f d).obj T) :
    relativePicardDegreeZeroSubgroup f T ≃ (relativePicardDegreeSubfunctor f d).obj T :=
  let a : (relativePicardPresheaf f).obj T := c.val
  { toFun z := z • c
    invFun c' :=
      let a' : (relativePicardPresheaf f).obj T := c'.val
      ⟨a' / a, div_mem_relativePicardDegreeZeroSubgroup f c.property c'.property⟩
    left_inv z := Subtype.ext (mul_div_cancel_right (z : (relativePicardPresheaf f).obj T) a)
    right_inv c' :=
      let a' : (relativePicardPresheaf f).obj T := c'.val
      Subtype.ext (div_mul_cancel a' a) }

/-- The bijection `relativePicardDegreeSubfunctorObjEquiv f c` is translation by `c`. -/
@[simp]
lemma relativePicardDegreeSubfunctorObjEquiv_apply {d : ℤ} {T : (Over S)ᵒᵖ}
    (c : (relativePicardDegreeSubfunctor f d).obj T) (z : relativePicardDegreeZeroSubgroup f T) :
    relativePicardDegreeSubfunctorObjEquiv f c z = z • c :=
  (rfl)

/-- The inverse of `relativePicardDegreeSubfunctorObjEquiv f c` divides by `c`. -/
@[simp]
lemma coe_relativePicardDegreeSubfunctorObjEquiv_symm_apply {d : ℤ} {T : (Over S)ᵒᵖ}
    {c c' : (relativePicardPresheaf f).obj T} (hc : c ∈ (relativePicardDegreeSubfunctor f d).obj T)
    (hc' : c' ∈ (relativePicardDegreeSubfunctor f d).obj T) :
    (((relativePicardDegreeSubfunctorObjEquiv f ⟨c, hc⟩).symm ⟨c', hc'⟩ :
      relativePicardDegreeZeroSubgroup f T) : (relativePicardPresheaf f).obj T) = c' / c :=
  (rfl)

/-- The action of `Pic⁰_{X/S}(T)` on `Pic^d_{X/S}(T)` is pretransitive: any two sections of
degree `d` differ by a class of `Pic⁰_{X/S}(T)`. This holds vacuously when `Pic^d_{X/S}(T)` is
empty. -/
instance (d : ℤ) (T : (Over S)ᵒᵖ) :
    MulAction.IsPretransitive (relativePicardDegreeZeroSubgroup f T)
      ((relativePicardDegreeSubfunctor f d).obj T) :=
  ⟨fun c c' ↦ ⟨(relativePicardDegreeSubfunctorObjEquiv f c).symm c',
    (relativePicardDegreeSubfunctorObjEquiv f c).apply_symm_apply c'⟩⟩

/-- **A section of degree `d` over the base trivializes `Pic^d_{X/S}`.** For a smooth proper
geometrically connected family of curves and a section `c₀` of `Pic^d_{X/S}` over `S` itself,
multiplication by the pullbacks of `c₀` is a natural isomorphism from `Pic⁰_{X/S}` onto
`Pic^d_{X/S}`, as presheaves of sets on schemes over `S`; on sections over `T` it is the
bijection `relativePicardDegreeSubfunctorObjEquiv` for the pullback of `c₀` to `T`. -/
def relativePicardDegreeZeroIsoDegree {d : ℤ}
    {c₀ : (relativePicardPresheaf f).obj (op (Over.mk (𝟙 S)))}
    (hc₀ : c₀ ∈ (relativePicardDegreeSubfunctor f d).obj (op (Over.mk (𝟙 S)))) :
    (relativePicardDegreeZeroSubfunctor f).toFunctor ≅
      (relativePicardDegreeSubfunctor f d).toFunctor :=
  NatIso.ofComponents (fun T ↦ ((Equiv.subtypeEquivRight fun _ ↦
      (mem_relativePicardDegreeZeroSubgroup_iff f).symm).trans
    (relativePicardDegreeSubfunctorObjEquiv f
      ((relativePicardDegreeSubfunctor f d).toFunctor.map (Over.mkIdTerminal.from T.unop).op
        ⟨c₀, hc₀⟩))).toIso) (by
    intro T T' φ
    ext z
    apply Subtype.ext
    -- The pullbacks of `c₀` are compatible, as `Over.mk (𝟙 S)` is terminal.
    have h : (Over.mkIdTerminal.from T.unop).op ≫ φ = (Over.mkIdTerminal.from T'.unop).op :=
      Quiver.Hom.unop_inj (Over.mkIdTerminal.hom_ext _ _)
    rw [← h]
    simp only [Functor.comp_obj, Subfunctor.toFunctor_obj, Subfunctor.toFunctor_map,
      Functor.comp_map, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, op_unop, Functor.map_comp,
      CommGrpCat.hom_comp, MonoidHom.coe_comp, TypeCat.ofHom_apply, Function.comp_apply,
      TypeCat.Fun.toFun_apply, comp_apply, Equiv.toIso_hom_hom_apply, Equiv.trans_apply]
    rw [relativePicardDegreeSubfunctorObjEquiv_apply, relativePicardDegreeSubfunctorObjEquiv_apply,
      coe_relativePicardDegreeZeroSubgroup_smul, coe_relativePicardDegreeZeroSubgroup_smul]
    simp only [Equiv.subtypeEquivRight_apply_coe, map_mul])

-- The evaluation lemmas of the natural isomorphisms below are not `@[simp]`: `simp` rewrites the
-- types of their values by `Functor.comp_obj` and `Subfunctor.toFunctor_obj`, after which their
-- left-hand sides no longer match.
/-- The trivialization `relativePicardDegreeZeroIsoDegree f hc₀` multiplies a section of
`Pic⁰_{X/S}` over `T` by the pullback of `c₀` to `T`. -/
lemma coe_relativePicardDegreeZeroIsoDegree_hom_app {d : ℤ}
    {c₀ : (relativePicardPresheaf f).obj (op (Over.mk (𝟙 S)))}
    (hc₀ : c₀ ∈ (relativePicardDegreeSubfunctor f d).obj (op (Over.mk (𝟙 S)))) {T : (Over S)ᵒᵖ}
    {z : (relativePicardPresheaf f).obj T} (hz : z ∈ (relativePicardDegreeZeroSubfunctor f).obj T) :
    ((relativePicardDegreeZeroIsoDegree f hc₀).hom.app T ⟨z, hz⟩).val =
      z * (relativePicardPresheaf f).map (Over.mkIdTerminal.from T.unop).op c₀ :=
  (rfl)

/-- The inverse of the trivialization `relativePicardDegreeZeroIsoDegree f hc₀` divides a section
of `Pic^d_{X/S}` over `T` by the pullback of `c₀` to `T`. -/
lemma coe_relativePicardDegreeZeroIsoDegree_inv_app {d : ℤ}
    {c₀ : (relativePicardPresheaf f).obj (op (Over.mk (𝟙 S)))}
    (hc₀ : c₀ ∈ (relativePicardDegreeSubfunctor f d).obj (op (Over.mk (𝟙 S)))) {T : (Over S)ᵒᵖ}
    {c : (relativePicardPresheaf f).obj T} (hc : c ∈ (relativePicardDegreeSubfunctor f d).obj T) :
    ((relativePicardDegreeZeroIsoDegree f hc₀).inv.app T ⟨c, hc⟩).val =
      c / (relativePicardPresheaf f).map (Over.mkIdTerminal.from T.unop).op c₀ :=
  (rfl)

end Smooth

section FieldPoint

variable [QuasiCompact f] [QuasiSeparated f] {L : Type u} [Field L] (g : Spec (.of L) ⟶ S)

/-- **`Pic^d_{X/S}` at a field-valued point.** For `f` quasi-compact and quasi-separated and a
point `g : Spec L ⟶ S`, a section of `Pic(X_L) / Pic(Spec L) = Pic(X_L)` at `g`, with
`X_L = Spec L ×_S X`, lies in `Pic^d_{X/S}` exactly when its line-bundle class on `X_L` has degree
`d` over `L`. The field `L` is arbitrary; it need not be perfect or algebraically closed. -/
theorem mem_relativePicardDegreeSubfunctor_obj_iff_eulerDegree_eq {d : ℤ}
    (c : (relativePicardPresheaf f).obj (op (Over.mk g))) :
    c ∈ (relativePicardDegreeSubfunctor f d).obj (op (Over.mk g)) ↔
      letI : (pullback g f).Over (Spec (.of L)) := ⟨pullback.fst g f⟩
      haveI : Subsingleton (LineBundleClass (op (Over.mk g)).unop.left) :=
        inferInstanceAs (Subsingleton (LineBundleClass (Spec (.of L))))
      LineBundleClass.eulerDegree L (X := pullback g f)
        (relativePicardPresheafObjMulEquiv f (op (Over.mk g)) c) = d := by
  simp only [mem_relativePicardDegreeSubfunctor_obj_iff, relativePicardFiberDegree_eq_eulerDegree]
  exact ⟨fun h ↦ h (AlgebraicClosure L)
    (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)))), fun h _ _ _ _ ↦ h⟩

end FieldPoint

section BaseChange

variable {S' : Scheme.{u}} (g : S' ⟶ S)

/-- **The base change comparison preserves and reflects `Pic^d`.** For `g : S' ⟶ S`, a section
of `T ↦ Pic(T ×_{S'} X') / Pic(T)`, for the base change `X' = S' ×_S X ⟶ S'`, has degree `d` on
every geometric fibre exactly when its image in `T ↦ Pic(T ×_S X) / Pic(T)` under
`relativePicardPresheafBaseChangeIso` does. -/
theorem relativePicardPresheafBaseChangeIso_hom_app_mem_relativePicardDegreeSubfunctor_obj_iff
    {d : ℤ} {T : (Over S')ᵒᵖ} {c : (relativePicardPresheaf (pullback.fst g f)).obj T} :
    (relativePicardPresheafBaseChangeIso f g).hom.app T c ∈
        (relativePicardDegreeSubfunctor f d).obj ((Over.map g).op.obj T) ↔
      c ∈ (relativePicardDegreeSubfunctor (pullback.fst g f) d).obj T := by
  refine (mem_relativePicardDegreeSubfunctor_obj_iff f).trans
    (Iff.trans ?_ (mem_relativePicardDegreeSubfunctor_obj_iff _).symm)
  refine forall_congr' fun Ω ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    forall_congr' fun ξ ↦ ?_
  exact Iff.of_eq (congrArg (· = d)
    (relativePicardFiberDegree_relativePicardPresheafBaseChangeIso_hom_app f g (T := T) ξ c))

/-- **Base change of `Pic^d`.** For `g : S' ⟶ S`, the degree-`d` subfunctor of the base change
`X' = S' ×_S X ⟶ S'` is `Pic^d_{X/S}` restricted to schemes over `S'` along `Over.map g`, by the
restriction of `relativePicardPresheafBaseChangeIso`, that is pullback along
`T ×_S X ≅ T ×_{S'} X'`. -/
def relativePicardDegreeSubfunctorBaseChangeIso (d : ℤ) :
    (relativePicardDegreeSubfunctor (pullback.fst g f) d).toFunctor ≅
      (Over.map g).op ⋙ (relativePicardDegreeSubfunctor f d).toFunctor :=
  NatIso.ofComponents (fun T ↦ (((forget CommGrpCat).mapIso
      ((relativePicardPresheafBaseChangeIso f g).app T)).toEquiv.subtypeEquiv fun _ ↦
        (relativePicardPresheafBaseChangeIso_hom_app_mem_relativePicardDegreeSubfunctor_obj_iff
          f g).symm).toIso) (by
    intro T T' φ
    ext c
    apply Subtype.ext
    exact NatTrans.naturality_apply (relativePicardPresheafBaseChangeIso f g).hom φ c.val)

/-- The base change isomorphism `relativePicardDegreeSubfunctorBaseChangeIso` is the comparison
`relativePicardPresheafBaseChangeIso` on sections. -/
lemma coe_relativePicardDegreeSubfunctorBaseChangeIso_hom_app {d : ℤ} {T : (Over S')ᵒᵖ}
    {c : (relativePicardPresheaf (pullback.fst g f)).obj T}
    (hc : c ∈ (relativePicardDegreeSubfunctor (pullback.fst g f) d).obj T) :
    ((relativePicardDegreeSubfunctorBaseChangeIso f g d).hom.app T ⟨c, hc⟩).val =
      (relativePicardPresheafBaseChangeIso f g).hom.app T c :=
  (rfl)

/-- The inverse of `relativePicardDegreeSubfunctorBaseChangeIso` is the inverse comparison
`relativePicardPresheafBaseChangeIso` on sections. -/
lemma coe_relativePicardDegreeSubfunctorBaseChangeIso_inv_app {d : ℤ} {T : (Over S')ᵒᵖ}
    {c : (relativePicardPresheaf f).obj ((Over.map g).op.obj T)}
    (hc : c ∈ (relativePicardDegreeSubfunctor f d).obj ((Over.map g).op.obj T)) :
    ((relativePicardDegreeSubfunctorBaseChangeIso f g d).inv.app T ⟨c, hc⟩).val =
      (relativePicardPresheafBaseChangeIso f g).inv.app T c :=
  (rfl)

end BaseChange

end

end TauCeti.AlgebraicGeometry
