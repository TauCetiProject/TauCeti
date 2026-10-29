/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AffineScheme
public import TauCeti.AlgebraicGeometry.ModularCurve.NaiveLevel
public import TauCeti.CategoryTheory.Aut.Representable
public import TauCeti.CategoryTheory.Monoidal.Cartesian.FunctorCategory

/-!
# Free actions on simultaneous moduli schemes

Let `𝒫` and `𝒬` be moduli problems over `Ell/B`, and let a group `G` act on `𝒬`. If an object
`V = (E_V/𝕄)` of `Ell/B` represents the simultaneous problem `(𝒫, 𝒬)`, then `G` acts on `V`
through its action on the second factor (`ModuliProblem.simultaneousAction`): by the Yoneda lemma
(`CategoryTheory.Functor.RepresentableBy.autMulEquiv`), `g` acts as the automorphism `σ_g` of `V`
such that pulling back the universal pair `(α, β)` along `σ_g` gives `(α, g • β)`.

In Katz and Mazur's proof that a relatively representable, affine, rigid moduli problem `𝒫` is
representable (KM 4.7.0), `𝒬` is a rigidifying problem, for instance the naive full level-three
problem `[Γ(3)]` with its action of `GL₂(𝔽₃)`, and `𝒫` is recovered as the quotient of the moduli
scheme `𝕄(𝒫, 𝒬) = V.base` by `G`. The key input is that this action is **free**: if `𝒫` is rigid
and `G` acts freely on `𝒬` over nonempty bases, then for `g ≠ 1` the automorphism of `𝕄(𝒫, 𝒬)`
induced by `σ_g` fixes no point with values in a nonempty scheme
(`ModuliProblem.IsRigid.eq_one_of_comp_simultaneousAction_base_eq`). Indeed, a point
`x : T ⟶ 𝕄(𝒫, 𝒬)` fixed by `g` gives an automorphism `τ` of the pulled-back curve `E_T` over `T`
which carries the pulled-back structure `(α_T, β_T)` to `(α_T, g • β_T)`. Rigidity of `𝒫` forces
`τ = 1`, so `g • β_T = β_T`, and freeness of the action on `𝒬` gives `g = 1`.

Rigidity of `𝒫` cannot be dropped. For the trivial problem `𝒫 = [Γ(1)]` and `𝒬 = [Γ(3)]`, the
automorphism `[-1]` of every elliptic curve carries a level-three basis `(P, Q)` to `(-P, -Q)`,
so the matrix `-1` of `GL₂(𝔽₃)` acts trivially on `𝕄([Γ(3)])`, although it acts freely on
level-three bases.

When `𝕄(𝒫, 𝒬)` is affine, freeness says equivalently that for `g ≠ 1` the elements `σ_g^*(a) - a`
generate the unit ideal of its ring of functions
(`ModuliProblem.IsRigid.span_range_appTop_simultaneousAction_sub_eq_top`, through
`AlgebraicGeometry.Scheme.Hom.span_range_appTop_sub_eq_top_iff`). Pullback reverses composition,
so a group `G` acts on this ring by `g • a = σ_{g⁻¹}^*(a)`
(`ModuliProblem.simultaneousSectionsAction`), and for `g ≠ 1` the elements `g • a - a` generate
the unit ideal (`ModuliProblem.IsRigid.span_range_smul_sub_eq_top`). For a finite group this is
the hypothesis under which the projection to the invariant quotient is a finite étale torsor
(`TauCeti.AffineInvariantQuotient.etale_projection`,
`TauCeti.AffineInvariantQuotient.isPullback_of_free`).

For the naive full level-`N` problem `[Γ(N)]`, on which `GL₂(ℤ/Nℤ)` acts freely over nonempty
bases (`ModuliProblem.eq_one_of_gammaNaiveAction_hom_app_eq_self`), this gives the freeness of the
action of `GL₂(ℤ/Nℤ)` on `𝕄(𝒫, [Γ(N)])` for every rigid `𝒫`
(`ModuliProblem.IsRigid.eq_one_of_comp_simultaneousAction_gammaNaiveAction_base_eq`), and its
form for functions on an affine `𝕄(𝒫, [Γ(N)])`
(`ModuliProblem.IsRigid.span_range_gammaNaiveAction_smul_sub_eq_top`).

## Main definitions

* `TauCeti.AlgebraicGeometry.ModuliProblem.simultaneousAction`: the action of `G` on an object
  representing `(𝒫, 𝒬)`, induced by an action of `G` on `𝒬`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.simultaneousSectionsAction`: for a group `G`, the
  induced action on the ring of functions `Γ(𝕄(𝒫, 𝒬), ⊤)`, by pullback along inverses.

## Main results

* `TauCeti.AlgebraicGeometry.ModuliProblem.homEquiv_comp_simultaneousAction_hom`: `σ_g` pulls the
  universal pair `(α, β)` back to `(α, g • β)`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.IsRigid.eq_one_of_comp_simultaneousAction_base_eq`:
  for rigid `𝒫` and a free action on `𝒬`, the action on `𝕄(𝒫, 𝒬)` has no fixed points with values
  in nonempty schemes.
* `TauCeti.AlgebraicGeometry.ModuliProblem.IsRigid.span_range_appTop_simultaneousAction_sub_eq_top`:
  when `𝕄(𝒫, 𝒬)` is affine, the same freeness in terms of its ring of functions.
* `TauCeti.AlgebraicGeometry.ModuliProblem.IsRigid.span_range_smul_sub_eq_top`: for a group, the
  same freeness for the action `simultaneousSectionsAction`, in the form taken by
  `TauCeti.AffineInvariantQuotient.etale_projection`.
* `ModuliProblem.IsRigid.eq_one_of_comp_simultaneousAction_gammaNaiveAction_base_eq`,
  `ModuliProblem.IsRigid.span_range_gammaNaiveAction_smul_sub_eq_top`:
  the case of `GL₂(ℤ/Nℤ)` acting on naive full level-`N` structures.

## References

* N. M. Katz, B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 2.7.2 and Chapter 4, proof of Theorem 4.7.0.
-/

public section

open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace ModuliProblem

variable {B : Scheme.{u}} {P Q : ModuliProblem B} {V : EllObj B} (R : (P ⊗ Q).RepresentableBy V)

section Monoid

variable {G : Type*} [Monoid G] (ρ : G →* Aut Q)

/-- **The action on the object representing a simultaneous problem.** If `G` acts on `𝒬` and `V`
represents the simultaneous problem `(𝒫, 𝒬)`, then `G` acts on `V` through its action on the
second factor: `g` acts as the automorphism `σ_g` of `V` along which the universal pair `(α, β)`
pulls back to `(α, g • β)` (`homEquiv_comp_simultaneousAction_hom`). -/
noncomputable def simultaneousAction : G →* Aut V :=
  R.autMulEquiv.toMonoidHom.comp (((tensorLeft P).mapAut Q).comp ρ)

/-- The automorphism `σ_g` of the object `V` representing `(𝒫, 𝒬)` acts on the pair of level
structures classified by an arrow `f : X ⟶ V` through the action of `g` on the second factor. -/
theorem homEquiv_comp_simultaneousAction_hom (g : G) {X : EllObj B} (f : X ⟶ V) :
    R.homEquiv (f ≫ (simultaneousAction R ρ g).asIso.hom) =
      ((R.homEquiv f).1, (ρ g).asIso.hom.app (op X) (R.homEquiv f).2) := by
  rw [simultaneousAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    R.homEquiv_comp_autMulEquiv_hom]
  -- `(tensorLeft P).mapAut Q` acts on `𝒫 ⊗ 𝒬` by whiskering, `P ◁ -`
  exact Prod.ext (Functor.Monoidal.whiskerLeft_app_apply_fst _ _)
    (Functor.Monoidal.whiskerLeft_app_apply_snd _ _)

/-- The inverse of the automorphism `σ_g` of the object `V` representing `(𝒫, 𝒬)` acts on the pair
of level structures classified by an arrow `f : X ⟶ V` through the inverse of the action of `g` on
the second factor. -/
theorem homEquiv_comp_simultaneousAction_inv (g : G) {X : EllObj B} (f : X ⟶ V) :
    R.homEquiv (f ≫ (simultaneousAction R ρ g).asIso.inv) =
      ((R.homEquiv f).1, (ρ g).asIso.inv.app (op X) (R.homEquiv f).2) := by
  rw [simultaneousAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    R.homEquiv_comp_autMulEquiv_inv]
  -- `(tensorLeft P).mapAut Q` acts on `𝒫 ⊗ 𝒬` by whiskering, `P ◁ -`
  exact Prod.ext (Functor.Monoidal.whiskerLeft_app_apply_fst _ _)
    (Functor.Monoidal.whiskerLeft_app_apply_snd _ _)

/-- **A rigid problem makes a free action on a rigidifier free on the simultaneous moduli scheme**
(the freeness step in Katz and Mazur's proof of Theorem 4.7.0). Let `𝒫` be rigid, let `G` act on
`𝒬` freely over nonempty bases, and let `V` represent `(𝒫, 𝒬)`. If a point `x : T ⟶ V.base` with
values in a nonempty scheme `T` is fixed by the automorphism of `𝕄(𝒫, 𝒬) = V.base` induced by
`g`, then `g = 1`. -/
theorem IsRigid.eq_one_of_comp_simultaneousAction_base_eq (hP : P.IsRigid)
    (hρ : ∀ (X : EllObj B), Nonempty X.base → ∀ (g : G) (β : Q.obj (op X)),
      (ρ g).asIso.hom.app (op X) β = β → g = 1)
    {T : Scheme.{u}} [Nonempty T] {x : T ⟶ V.base} {g : G}
    (hx : x ≫ (simultaneousAction R ρ g).asIso.hom.base = x) : g = 1 := by
  -- Pull `V` back along `x` to `X = (E_T/T)`, with its arrow `e : X ⟶ V` over `x`. The arrows
  -- `e` and `e ≫ σ_g` both lie over `x`, so they differ by an automorphism `τ` of `X` over `T`.
  let e := V.baseChangeFunctorHom (Over.mk x)
  let s := (simultaneousAction R ρ g).asIso.hom
  let τ := EllObj.Hom.lift e (e ≫ s) (𝟙 _) (by
    simp only [e, s, EllObj.comp_base, EllObj.baseChangeFunctorHom_base, Over.mk_hom]
    exact (Category.id_comp x).trans hx.symm)
  have h := R.homEquiv_comp τ e
  rw [show τ ≫ e = e ≫ s from EllObj.Hom.lift_comp _ _ _ _,
    homEquiv_comp_simultaneousAction_hom] at h
  obtain ⟨hα, hβ⟩ := Prod.ext_iff.1 h
  simp only [Functor.Monoidal.tensorObj_map_apply_fst,
    Functor.Monoidal.tensorObj_map_apply_snd] at hα hβ
  -- `τ` fixes the `𝒫`-structure, so it is the identity by rigidity; then `g` fixes the
  -- `𝒬`-structure over the nonempty base `T`.
  have hτ : τ = 𝟙 _ := P.isRigid_iff.1 hP τ (EllObj.Hom.lift_base _ _ _ _) _ hα.symm
  rw [hτ, op_id, Functor.map_id_apply] at hβ
  exact hρ (V.baseChangeFunctor.obj (Over.mk x)) ‹Nonempty T› g _ hβ

/-- **Freeness on an affine simultaneous moduli scheme, in terms of functions.** Let `𝒫` be rigid,
let `G` act on `𝒬` freely over nonempty bases, and let `V` represent `(𝒫, 𝒬)` with `𝕄(𝒫, 𝒬) =
V.base` affine. For `g ≠ 1`, the elements `σ_g^*(a) - a` of `Γ(𝕄(𝒫, 𝒬), ⊤)` generate the unit
ideal. For a group, `IsRigid.span_range_smul_sub_eq_top` restates this for the action
`g • a = σ_{g⁻¹}^*(a)`, in the form taken by the invariant quotient by a finite group
(`TauCeti.AffineInvariantQuotient.etale_projection`). -/
theorem IsRigid.span_range_appTop_simultaneousAction_sub_eq_top (hP : P.IsRigid)
    (hρ : ∀ (X : EllObj B), Nonempty X.base → ∀ (g : G) (β : Q.obj (op X)),
      (ρ g).asIso.hom.app (op X) β = β → g = 1)
    [IsAffine V.base] {g : G} (hg : g ≠ 1) :
    Ideal.span (Set.range fun a : Γ(V.base, ⊤) ↦
      (simultaneousAction R ρ g).asIso.hom.base.appTop a - a) = ⊤ :=
  (Scheme.Hom.span_range_appTop_sub_eq_top_iff _).2 fun _ _ hx ↦
    not_nonempty_iff.1 fun _ ↦ hg (hP.eq_one_of_comp_simultaneousAction_base_eq R ρ hρ hx)

/-- **`GL₂(ℤ/Nℤ)` acts freely on `𝕄(𝒫, [Γ(N)])`** for every rigid `𝒫`. Let `V` represent the
simultaneous problem `(𝒫, [Γ(N)])` with the naive full level-`N` problem, on which `GL₂(ℤ/Nℤ)` acts
by change of basis. If a point of `V.base` with values in a nonempty scheme is fixed by a matrix
`g`, then `g = 1`. For `N = 3` this is the freeness of the action of `GL₂(𝔽₃)` on the moduli scheme
of `𝒫` rigidified by naive level-three structures. -/
theorem IsRigid.eq_one_of_comp_simultaneousAction_gammaNaiveAction_base_eq {N : ℕ}
    (hP : P.IsRigid) (R : (P ⊗ gammaNaive B N).RepresentableBy V) {T : Scheme.{u}} [Nonempty T]
    {x : T ⟶ V.base} {g : (GL (Fin 2) (ZMod N))ᵐᵒᵖ}
    (hx : x ≫ (simultaneousAction R (gammaNaiveAction B N) g).asIso.hom.base = x) : g = 1 :=
  hP.eq_one_of_comp_simultaneousAction_base_eq R _
    (fun _ _ _ _ h ↦ eq_one_of_gammaNaiveAction_hom_app_eq_self h) hx

end Monoid

section Group

variable {G : Type*} [Group G] (ρ : G →* Aut Q)

/-- **The action on the functions of the simultaneous moduli scheme.** If a group `G` acts on `𝒬`
and `V` represents `(𝒫, 𝒬)`, then `G` acts on the ring of functions `Γ(𝕄(𝒫, 𝒬), ⊤)` by pullback
along inverses, `g • a = σ_{g⁻¹}^*(a)` (`simultaneousSectionsAction_smul_def`). For finite `G`
and affine `𝕄(𝒫, 𝒬)`, `TauCeti.AffineInvariantQuotient` forms the quotient by this action. -/
@[instance_reducible]
noncomputable def simultaneousSectionsAction : MulSemiringAction G Γ(V.base, ⊤) :=
  Scheme.globalSectionsMulSemiringAction
    (((EllObj.forget B ⋙ Over.forget B).mapAut V).comp (simultaneousAction R ρ))

/-- Under `simultaneousSectionsAction R ρ`, `g` acts on a function on `𝕄(𝒫, 𝒬)` by pullback along
the automorphism of `𝕄(𝒫, 𝒬)` induced by `σ_{g⁻¹}`. -/
@[simp]
theorem simultaneousSectionsAction_smul_def (g : G) (a : Γ(V.base, ⊤)) :
    letI := simultaneousSectionsAction R ρ
    g • a = (simultaneousAction R ρ g⁻¹).asIso.hom.base.appTop a :=
  Scheme.globalSectionsMulSemiringAction_smul_def _ g a

/-- **Freeness on an affine simultaneous moduli scheme, for the action on functions.** Let `𝒫` be
rigid, let a group `G` act on `𝒬` freely over nonempty bases, and let `V` represent `(𝒫, 𝒬)` with
`𝕄(𝒫, 𝒬) = V.base` affine. For `g ≠ 1`, the elements `g • a - a` of `Γ(𝕄(𝒫, 𝒬), ⊤)` generate the
unit ideal, for the action `simultaneousSectionsAction`. For finite `G` this is the freeness
hypothesis of `TauCeti.AffineInvariantQuotient.etale_projection` and
`TauCeti.AffineInvariantQuotient.isPullback_of_free`. -/
theorem IsRigid.span_range_smul_sub_eq_top (hP : P.IsRigid)
    (hρ : ∀ (X : EllObj B), Nonempty X.base → ∀ (g : G) (β : Q.obj (op X)),
      (ρ g).asIso.hom.app (op X) β = β → g = 1)
    [IsAffine V.base] {g : G} (hg : g ≠ 1) :
    letI := simultaneousSectionsAction R ρ
    Ideal.span (Set.range fun a : Γ(V.base, ⊤) ↦ g • a - a) = ⊤ := by
  simpa only [simultaneousSectionsAction_smul_def] using
    hP.span_range_appTop_simultaneousAction_sub_eq_top R ρ hρ (inv_ne_one.2 hg)

/-- **`GL₂(ℤ/Nℤ)` acts freely on the functions of an affine `𝕄(𝒫, [Γ(N)])`** for every rigid `𝒫`.
Let `V` represent the simultaneous problem `(𝒫, [Γ(N)])` with `V.base` affine. For a matrix
`g ≠ 1`, the elements `g • a - a` of `Γ(V.base, ⊤)` generate the unit ideal, for the action
`simultaneousSectionsAction`. For `N = 3` this is the freeness hypothesis of the invariant quotient
of the moduli scheme of `𝒫` rigidified by naive level-three structures by `GL₂(𝔽₃)`. -/
theorem IsRigid.span_range_gammaNaiveAction_smul_sub_eq_top {N : ℕ} (hP : P.IsRigid)
    (R : (P ⊗ gammaNaive B N).RepresentableBy V) [IsAffine V.base]
    {g : (GL (Fin 2) (ZMod N))ᵐᵒᵖ} (hg : g ≠ 1) :
    letI := simultaneousSectionsAction R (gammaNaiveAction B N)
    Ideal.span (Set.range fun a : Γ(V.base, ⊤) ↦ g • a - a) = ⊤ :=
  hP.span_range_smul_sub_eq_top R _
    (fun _ _ _ _ h ↦ eq_one_of_gammaNaiveAction_hom_app_eq_self h) hg

end Group

end ModuliProblem

end TauCeti.AlgebraicGeometry
