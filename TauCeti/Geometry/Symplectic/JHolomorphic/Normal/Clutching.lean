/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.FlatLine.Trivial
public import TauCeti.Geometry.Symplectic.JHolomorphic.Normal.FlatLine
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Pullback
import TauCeti.Algebra.Module.ZLattice.AddChar
import TauCeti.Analysis.Calculus.DifferentialForm.Const

/-!
# Clutching flat lines over a torus: gauge transformations and the trivial line

Let `L ⊆ ℂ` be a lattice and `ψ : L → S¹` a unitary character. The flat line of holonomy `ψ`
over the torus `ℂ / L` (`TauCeti.FlatLine ψ`) is the orbit space of `ℂ × ℂ` under
`γ +ᵥ (z, v) = (z + γ, ψ γ v)`, with the complex structure and the Kähler coupling form
(`TauCeti.FlatLine.couplingForm`) induced from the cover, on which the connection is trivial. This
file compares it, as a line with connection, with the topologically trivial line
`(ℂ / L) × ℂ` carrying a constant flat connection `d + i ℓ`.

**Gauge transformations.** Let `ℓ : ℂ → ℝ` be real linear and suppose that the holonomies differ
by `exp (i ℓ)`: `ψ' γ = ψ γ exp (i ℓ(γ))` for every `γ ∈ L`. The gauge transformation
`(z, v) ↦ (z, exp (i ℓ(z)) v)` of the trivial line over `ℂ` (`TauCeti.normalModelGauge`) carries
the action of `γ` for `ψ` to its action for `ψ'`, since `ℓ(z + γ) = ℓ(z) + ℓ(γ)`. So it descends
to a diffeomorphism `TauCeti.FlatLine.gauge ℓ h : FlatLine ψ ≃ FlatLine ψ'` over the torus
(`TauCeti.FlatLine.proj_gauge`), multiplying each fibre by a unit complex number; these compose
by adding the linear forms (`TauCeti.FlatLine.gauge_trans_gauge`). In general it is not
holomorphic for the complex structures of the two flat lines: on the cover it carries the
connection `d + i ℓ` to the trivial connection, so it identifies the structures of `FlatLine ψ'`
with the normal model structures of `d + i ℓ` on `FlatLine ψ`. Read on the cover of
`FlatLine ψ`, for a one-form `A` with `A(v) = ℓ(v)`,

* the gauge transformation pulls the complex structure of `FlatLine ψ'` back to the normal model
  structure `J_N` of the connection `d + i A`
  (`TauCeti.FlatLine.pullback_gauge_mfderiv_mk_eq_normalModelStructure`);
* it pulls the coupling form of `FlatLine ψ'` back to the coupling form
  `π^* ω_ℂ + d((|v|² / 2) (dθ + A))` of `d + i A`
  (`TauCeti.FlatLine.eval₂_mpullback_gauge_couplingForm_mfderiv_mk_eq_normalCouplingForm`).

**The trivial line.** For the trivial character the flat line is the product line
`(ℂ / L) × ℂ` (`TauCeti.FlatLine.prodDiffeomorph`). If `ψ γ = exp (i ℓ(γ))` for a real-linear
`ℓ`, the gauge transformation of `-ℓ` followed by this identification is a trivialization
`TauCeti.FlatLine.trivialization ℓ h : FlatLine ψ ≃ (ℂ / L) × ℂ` of the flat line, sending
`[(z, v)]` to `([z], exp (-i ℓ(z)) v)`. For a full lattice every unitary character has this
form (`AddChar.exists_continuousLinearMap_forall_apply_eq_circleExp`), so every flat line over a
torus is smoothly trivial (`TauCeti.FlatLine.exists_diffeomorph_forall_fst_eq_proj`).

Together, these say that the Kähler model `(FlatLine ψ, J, ω_N)` of a flat line with holonomy
`exp (i ℓ)` is the trivial line over the torus with the normal model structure and the coupling
form of the constant connection `d + i ℓ`, transported by an explicit clutching. This is the
form in which Taubes normalizes a neighbourhood of an embedded square-zero torus: its normal line
is topologically trivial, with a flat unitary connection of irrational holonomy.

## Main definitions

* `TauCeti.FlatLine.gauge`: the gauge transformation `FlatLine ψ ≃ FlatLine ψ'` of a linear form
  `ℓ` with `ψ' = ψ exp (i ℓ)`.
* `TauCeti.FlatLine.trivialization`: the trivialization of the flat line of `exp (i ℓ)`.

## Main results

* `TauCeti.FlatLine.pullback_gauge_mfderiv_mk_eq_normalModelStructure`: the gauge transformation
  pulls the complex structure back to the normal model structure of the connection.
* `TauCeti.FlatLine.eval₂_mpullback_gauge_couplingForm_mfderiv_mk_eq_normalCouplingForm`: it pulls
  the coupling form back to the coupling form of the connection.
* `TauCeti.FlatLine.exists_diffeomorph_forall_fst_eq_proj`: every flat line over a complex torus
  is smoothly trivial.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Appendix B and Section 2.1
  (factors of automorphy, and their change by a coboundary under a change of trivialization).
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893 (square-zero tori and the flat model of their normal bundles).
-/

public noncomputable section

open Complex Function
open scoped Manifold ContDiff

namespace TauCeti

namespace FlatLine

variable {L : Submodule ℤ ℂ} {ψ ψ' ψ'' : AddChar L Circle} {ℓ ℓ' : ℂ →L[ℝ] ℝ}

/-- The gauge transformation of `ℓ` carries the action of `γ` for `ψ` to its action for `ψ'`,
read on the orbit projection. -/
private theorem mk_normalModelGauge_add_mul (h : ∀ γ, ψ' γ = ψ γ * Circle.exp (ℓ γ)) (z v : ℂ)
    (γ : L) :
    (Quotient.mk _ (normalModelGauge ℓ (z + γ, (ψ γ : ℂ) * v)) : FlatLine ψ') =
      Quotient.mk _ (normalModelGauge ℓ (z, v)) := by
  have key : exp (ℓ (z + γ) * I) * ((ψ γ : ℂ) * v) = ψ' γ * (exp (ℓ z * I) * v) := by
    simp only [h, map_add, ofReal_add, add_mul, Complex.exp_add, Circle.coe_mul, Circle.coe_exp]
    ring
  rw [normalModelGauge_def, normalModelGauge_def, key]
  exact mk_add_mul _ _ γ

variable (ℓ) in
/-- The map of flat lines induced by the gauge transformation of `ℓ`. -/
private def gaugeFun (h : ∀ γ, ψ' γ = ψ γ * Circle.exp (ℓ γ)) : FlatLine ψ → FlatLine ψ' :=
  Quotient.lift (fun p ↦ Quotient.mk _ (normalModelGauge ℓ p)) fun p q hpq ↦ by
    obtain ⟨γ, h₁, h₂⟩ := mk_eq_mk_iff.1 (Quotient.sound hpq : (Quotient.mk _ p : FlatLine ψ) =
      Quotient.mk _ q)
    obtain ⟨p₁, p₂⟩ := p
    dsimp only at h₁ h₂ ⊢
    subst h₁ h₂
    exact mk_normalModelGauge_add_mul h q.1 q.2 γ

private theorem gaugeFun_mk (h : ∀ γ, ψ' γ = ψ γ * Circle.exp (ℓ γ)) (p : ℂ × ℂ) :
    gaugeFun ℓ h (Quotient.mk _ p) = Quotient.mk _ (normalModelGauge ℓ p) :=
  rfl

/-- The holonomies of `ψ'` and `ψ` differ by `exp (i (-ℓ))` in the other direction. -/
private theorem neg_holonomy (h : ∀ γ, ψ' γ = ψ γ * Circle.exp (ℓ γ)) (γ : L) :
    ψ γ = ψ' γ * Circle.exp ((-ℓ) γ) := by
  rw [h, neg_apply, Circle.exp_neg, mul_inv_cancel_right]

private theorem gaugeFun_neg_gaugeFun (h : ∀ γ, ψ' γ = ψ γ * Circle.exp (ℓ γ)) (x : FlatLine ψ) :
    gaugeFun (-ℓ) (neg_holonomy h) (gaugeFun ℓ h x) = x := by
  obtain ⟨p, rfl⟩ := Quotient.mk_surjective x
  rw [gaugeFun_mk, gaugeFun_mk, FunLike.coe_neg, normalModelGauge_neg_normalModelGauge]

private theorem gaugeFun_gaugeFun_neg (h : ∀ γ, ψ' γ = ψ γ * Circle.exp (ℓ γ)) (x : FlatLine ψ') :
    gaugeFun ℓ h (gaugeFun (-ℓ) (neg_holonomy h) x) = x := by
  obtain ⟨p, rfl⟩ := Quotient.mk_surjective x
  rw [gaugeFun_mk, gaugeFun_mk, FunLike.coe_neg, normalModelGauge_normalModelGauge_neg]

/-- The holonomy of the trivial character differs from `exp (i ℓ)` by `exp (-i ℓ)`. -/
private theorem one_holonomy (h : ∀ γ, ψ γ = Circle.exp (ℓ γ)) (γ : L) :
    (1 : AddChar L Circle) γ = ψ γ * Circle.exp ((-ℓ) γ) := by
  rw [h, neg_apply, Circle.exp_neg, mul_inv_cancel, one_apply]

variable [DiscreteTopology L] {n : WithTop ℕ∞}

private theorem contMDiff_gaugeFun (h : ∀ γ, ψ' γ = ψ γ * Circle.exp (ℓ γ)) :
    ContMDiff 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℂ × ℂ) n (gaugeFun ℓ h) := by
  rw [← (isLocalDiffeomorph_addQuotientMk (G := FlatLineLattice ψ) (I := 𝓘(ℝ, ℂ × ℂ))
    (n := n)).contMDiff_comp_iff Quotient.mk_surjective le_rfl]
  exact isLocalDiffeomorph_addQuotientMk.contMDiff.comp
    (contDiff_normalModelGauge ℓ.contDiff).contMDiff

variable (ℓ) in
/-- **The gauge transformation of flat lines.** Let `ℓ` be a real-linear form on `ℂ` and let the
holonomies of `ψ` and `ψ'` differ by `exp (i ℓ)`, `ψ' γ = ψ γ exp (i ℓ(γ))`. The gauge
transformation `(z, v) ↦ (z, exp (i ℓ(z)) v)` of `ℂ × ℂ` descends to this diffeomorphism
`[(z, v)] ↦ [(z, exp (i ℓ(z)) v)]` from the flat line of `ψ` to that of `ψ'`, over the identity of
the torus (`TauCeti.FlatLine.proj_gauge`). Its inverse is the gauge transformation of `-ℓ`
(`TauCeti.FlatLine.gauge_symm`). -/
def gauge (h : ∀ γ, ψ' γ = ψ γ * Circle.exp (ℓ γ)) :
    FlatLine ψ ≃ₘ^n⟮𝓘(ℝ, ℂ × ℂ), 𝓘(ℝ, ℂ × ℂ)⟯ FlatLine ψ' where
  toFun := gaugeFun ℓ h
  invFun := gaugeFun (-ℓ) (neg_holonomy h)
  left_inv := gaugeFun_neg_gaugeFun h
  right_inv := gaugeFun_gaugeFun_neg h
  contMDiff_toFun := contMDiff_gaugeFun h
  contMDiff_invFun := contMDiff_gaugeFun (neg_holonomy h)

/-- The gauge transformation sends `[(z, v)]` to `[(z, exp (i ℓ(z)) v)]`. -/
@[simp]
theorem gauge_mk (h : ∀ γ, ψ' γ = ψ γ * Circle.exp (ℓ γ)) (p : ℂ × ℂ) :
    gauge (n := n) ℓ h (Quotient.mk _ p) = Quotient.mk _ (normalModelGauge ℓ p) :=
  (rfl)

/-- The gauge transformation commutes with the projections to the torus. -/
@[simp]
theorem proj_gauge (h : ∀ γ, ψ' γ = ψ γ * Circle.exp (ℓ γ)) (x : FlatLine ψ) :
    proj (gauge (n := n) ℓ h x) = proj x := by
  obtain ⟨p, rfl⟩ := Quotient.mk_surjective x
  simp

/-- The inverse of the gauge transformation of `ℓ` is the gauge transformation of `-ℓ`. -/
theorem gauge_symm (h : ∀ γ, ψ' γ = ψ γ * Circle.exp (ℓ γ))
    (h' : ∀ γ, ψ γ = ψ' γ * Circle.exp ((-ℓ) γ)) :
    (gauge (n := n) ℓ h).symm = gauge (-ℓ) h' := by
  ext x
  exact (gauge ℓ h).symm_apply_eq.2 (gaugeFun_gaugeFun_neg h x).symm

/-- Gauge transformations compose by adding their linear forms. -/
theorem gauge_trans_gauge (h : ∀ γ, ψ' γ = ψ γ * Circle.exp (ℓ γ))
    (h' : ∀ γ, ψ'' γ = ψ' γ * Circle.exp (ℓ' γ))
    (h'' : ∀ γ, ψ'' γ = ψ γ * Circle.exp ((ℓ' + ℓ) γ)) :
    (gauge (n := n) ℓ h).trans (gauge ℓ' h') = gauge (ℓ' + ℓ) h'' := by
  ext x
  obtain ⟨p, rfl⟩ := Quotient.mk_surjective x
  simp [normalModelGauge_normalModelGauge]

/-! ### The trivial line -/

variable (ℓ) in
/-- **The trivialization of a flat line.** If `ψ γ = exp (i ℓ(γ))` for a real-linear form `ℓ` on
`ℂ`, the flat line of `ψ` is diffeomorphic to the product line `(ℂ / L) × ℂ` over the torus, by
`[(z, v)] ↦ ([z], exp (-i ℓ(z)) v)`: the gauge transformation of `-ℓ` onto the flat line of the
trivial character, followed by `TauCeti.FlatLine.prodDiffeomorph`. -/
def trivialization (h : ∀ γ, ψ γ = Circle.exp (ℓ γ)) :
    FlatLine ψ ≃ₘ^n⟮𝓘(ℝ, ℂ × ℂ), 𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)⟯ AddAction.orbitRel.Quotient L ℂ × ℂ :=
  (gauge (-ℓ) (one_holonomy h)).trans prodDiffeomorph

/-- The trivialization sends `[(z, v)]` to `([z], exp (-i ℓ(z)) v)`. -/
@[simp]
theorem trivialization_mk (h : ∀ γ, ψ γ = Circle.exp (ℓ γ)) (p : ℂ × ℂ) :
    trivialization (n := n) ℓ h (Quotient.mk _ p) =
      (Quotient.mk _ p.1, exp (-ℓ p.1 * I) * p.2) := by
  simp [trivialization]

/-- The inverse of the trivialization sends `([z], w)` to `[(z, exp (i ℓ(z)) w)]`. -/
@[simp]
theorem trivialization_symm_mk (h : ∀ γ, ψ γ = Circle.exp (ℓ γ)) (z w : ℂ) :
    (trivialization (n := n) ℓ h).symm (Quotient.mk _ z, w) =
      Quotient.mk _ (z, exp (ℓ z * I) * w) := by
  simp [trivialization, gauge_symm _ (neg_holonomy (one_holonomy h)), normalModelGauge_def]

/-- The trivialization is a map over the torus. -/
@[simp]
theorem fst_trivialization (h : ∀ γ, ψ γ = Circle.exp (ℓ γ)) (x : FlatLine ψ) :
    (trivialization (n := n) ℓ h x).1 = proj x := by
  obtain ⟨p, rfl⟩ := Quotient.mk_surjective x
  simp

/-- **Every flat line over a complex torus is smoothly trivial**: the flat line of any unitary
character of a full lattice `L` is diffeomorphic, over the torus `ℂ / L`, to the product line
`(ℂ / L) × ℂ`. -/
theorem exists_diffeomorph_forall_fst_eq_proj [IsZLattice ℝ L] (ψ : AddChar L Circle) :
    ∃ e : FlatLine ψ ≃ₘ^n⟮𝓘(ℝ, ℂ × ℂ), 𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)⟯
      AddAction.orbitRel.Quotient L ℂ × ℂ, ∀ x, (e x).1 = proj x := by
  obtain ⟨ℓ, h⟩ := ψ.exists_continuousLinearMap_forall_apply_eq_circleExp
  exact ⟨trivialization ℓ h, fst_trivialization h⟩

/-! ### The complex structure and the coupling form -/

variable {ω₀ : ℂ → ℂ [⋀^Fin 2]→L[ℝ] ℝ} {A : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ}

/-- A one-form on `ℂ` whose values on constant vectors are those of `ℓ` is constant. -/
private theorem eq_const_of_apply (hA : ∀ z v, A z (fun _ ↦ v) = ℓ v) (z : ℂ) :
    A z = A 0 := by
  ext m
  have hm : m = fun _ ↦ m 0 := funext fun i ↦ congrArg m (Subsingleton.elim i 0)
  rw [hm, hA, hA]

/-- The differential of the gauge transformation, read through the orbit projections, is the
derivative of `normalModelGauge ℓ` on `ℂ × ℂ`. -/
private theorem mfderiv_gauge_mfderiv_mk (h : ∀ γ, ψ' γ = ψ γ * Circle.exp (ℓ γ))
    (p v : ℂ × ℂ) :
    mfderiv 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℂ × ℂ) (gauge (n := ∞) ℓ h)
        (Quotient.mk _ p) (mfderiv 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℂ × ℂ)
          (Quotient.mk (AddAction.orbitRel (FlatLineLattice ψ) (ℂ × ℂ))) p v) =
      mfderiv 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℂ × ℂ)
        (Quotient.mk (AddAction.orbitRel (FlatLineLattice ψ') (ℂ × ℂ)))
        (normalModelGauge ℓ p) (fderiv ℝ (normalModelGauge ℓ) p v) := by
  have hq := isLocalDiffeomorph_addQuotientMk (G := FlatLineLattice ψ) (I := 𝓘(ℝ, ℂ × ℂ))
    (M := ℂ × ℂ) (n := ∞)
  have hq' := isLocalDiffeomorph_addQuotientMk (G := FlatLineLattice ψ') (I := 𝓘(ℝ, ℂ × ℂ))
    (M := ℂ × ℂ) (n := ∞)
  have hg : MDifferentiableAt 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℂ × ℂ) (normalModelGauge ℓ) p :=
    ((contDiff_normalModelGauge (n := ∞) ℓ.contDiff).contMDiff.mdifferentiable
      (by simp)) p
  have hcomp : (gauge (n := ∞) ℓ h) ∘ Quotient.mk _ =
      Quotient.mk (AddAction.orbitRel (FlatLineLattice ψ') (ℂ × ℂ)) ∘ normalModelGauge ℓ :=
    funext fun _ ↦ gauge_mk h _
  calc _ = mfderiv 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℂ × ℂ) ((gauge (n := ∞) ℓ h) ∘ Quotient.mk _) p v :=
        (mfderiv_comp_apply p (((gauge ℓ h).contMDiff.mdifferentiable (by simp)) _)
          ((hq.contMDiff.mdifferentiable (by simp)) p) v).symm
    _ = _ := by
      rw [hcomp]
      exact (mfderiv_comp_apply p ((hq'.contMDiff.mdifferentiable (by simp)) _) hg v).trans
        -- `mfderiv_eq_fderiv` conjugates by the identifications of the tangent spaces of
        -- `ℂ × ℂ` with `ℂ × ℂ` itself, which are the identity.
        (by rw [mfderiv_eq_fderiv]; rfl)

/-- **The gauge transformation pulls the complex structure back to the normal model structure of
the connection.** Let the holonomies of `ψ` and `ψ'` differ by `exp (i ℓ)`, and let `A` be the
one-form `ℓ` on `ℂ`. Read on the cover `ℂ × ℂ` of the flat line of `ψ`, the pullback along the
gauge transformation of the complex structure of the flat line of `ψ'` is the normal model
structure `J_N` of the connection `d + i A`. -/
theorem pullback_gauge_mfderiv_mk_eq_normalModelStructure
    (h : ∀ γ, ψ' γ = ψ γ * Circle.exp (ℓ γ))
    (hA : ∀ z v, A z (fun _ ↦ v) = ℓ v) (p v : ℂ × ℂ) :
    SmoothAlmostComplexStructure.pullback (gauge ℓ h)
        (SmoothAlmostComplexStructure.ofComplexManifold (ℂ × ℂ) (FlatLine ψ'))
        (Quotient.mk _ p) (mfderiv 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℂ × ℂ)
          (Quotient.mk (AddAction.orbitRel (FlatLineLattice ψ) (ℂ × ℂ))) p v) =
      mfderiv 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℂ × ℂ)
        (Quotient.mk (AddAction.orbitRel (FlatLineLattice ψ) (ℂ × ℂ))) p
        (normalModelStructure (normalModelConnectionCoeff A) 0 p v) := by
  -- The differential of `normalModelGauge ℓ` is complex linear from the normal model structure of
  -- `A` to the standard structure of `ℂ × ℂ`.
  have hlin : fderiv ℝ (normalModelGauge ℓ) p
      (normalModelStructure (normalModelConnectionCoeff A) 0 p v) =
        I • fderiv ℝ (normalModelGauge ℓ) p v := by
    have hJ := (isJHolomorphicAt_normalModelGauge (A := A) (A' := 0) ℓ.differentiableAt (p := p)
      fun v ↦ by simp [hA, ℓ.fderiv]).fderiv_apply_commute (v := v)
    simpa using hJ
  -- The orbit projection of the flat line of `ψ'` is holomorphic.
  have hmk := (isLocalDiffeomorph_addQuotientMk (G := FlatLineLattice ψ') (I := 𝓘(ℂ, ℂ × ℂ))
    (M := ℂ × ℂ) (n := ⊤)).contMDiff.mdifferentiable (by simp) (normalModelGauge ℓ p)
  have hinj : Injective (mfderiv 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℂ × ℂ) (gauge (n := ∞) ℓ h)
      (Quotient.mk _ p)) :=
    ((gauge (n := ∞) ℓ h).isInvertible_mfderiv (by simp)).injective
  apply hinj
  -- Read the differential of the gauge transformation on the covers.
  rw [mfderiv_gauge_mfderiv_mk h p]
  calc _ = SmoothAlmostComplexStructure.ofComplexManifold (ℂ × ℂ) (FlatLine ψ')
          (Quotient.mk _ (normalModelGauge ℓ p))
          (mfderiv 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℂ × ℂ)
            (Quotient.mk (AddAction.orbitRel (FlatLineLattice ψ') (ℂ × ℂ))) (normalModelGauge ℓ p)
            (fderiv ℝ (normalModelGauge ℓ) p v)) := by
        -- The gauge transformation is complex linear from the pullback to the structure of the
        -- flat line of `ψ'`.
        rw [SmoothAlmostComplexStructure.mfderiv_pullback_apply, mfderiv_gauge_mfderiv_mk, gauge_mk]
    -- The orbit projection of the flat line of `ψ'` is holomorphic, so it commutes with `i`.
    _ = mfderiv 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℂ × ℂ)
          (Quotient.mk (AddAction.orbitRel (FlatLineLattice ψ') (ℂ × ℂ))) (normalModelGauge ℓ p)
          (SmoothAlmostComplexStructure.ofComplexManifold (ℂ × ℂ) (ℂ × ℂ) (normalModelGauge ℓ p)
            (fderiv ℝ (normalModelGauge ℓ) p v)) :=
        (hmk.mfderiv_ofComplexManifold_apply _).symm
    -- The differential of `normalModelGauge ℓ` carries `J_N` to multiplication by `i`.
    _ = mfderiv 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℂ × ℂ)
          (Quotient.mk (AddAction.orbitRel (FlatLineLattice ψ') (ℂ × ℂ))) (normalModelGauge ℓ p)
          (fderiv ℝ (normalModelGauge ℓ) p
            (normalModelStructure (normalModelConnectionCoeff A) 0 p v)) := by
        rw [SmoothAlmostComplexStructure.ofComplexManifold_apply, hlin]

/-- **The gauge transformation pulls the coupling form back to the coupling form of the
connection.** Let the holonomies of `ψ` and `ψ'` differ by `exp (i ℓ)`, let `A` be the one-form
`ℓ` on `ℂ`, and let `ω₀` be the area form of `ℂ`. Read on the cover `ℂ × ℂ` of the flat line of
`ψ`, the pullback along the gauge transformation of the coupling form of the flat line of `ψ'` is
the coupling form `π^* ω₀ + d((|v|² / 2) (dθ + A))` of the connection `d + i A`. -/
theorem eval₂_mpullback_gauge_couplingForm_mfderiv_mk_eq_normalCouplingForm
    (h : ∀ γ, ψ' γ = ψ γ * Circle.exp (ℓ γ))
    (hω₀ : ∀ z v v', ω₀ z ![v, v'] = stdComplexSymplecticForm v v')
    (hA : ∀ z v, A z (fun _ ↦ v) = ℓ v) (p u w : ℂ × ℂ) :
    (SmoothForm.mpullback (gauge ℓ h) (gauge ℓ h).contMDiff (couplingForm ψ')).eval₂
        (Quotient.mk _ p)
        (mfderiv 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℂ × ℂ)
          (Quotient.mk (AddAction.orbitRel (FlatLineLattice ψ) (ℂ × ℂ))) p u)
        (mfderiv 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℂ × ℂ)
          (Quotient.mk (AddAction.orbitRel (FlatLineLattice ψ) (ℂ × ℂ))) p w) =
      normalCouplingForm ω₀ A p ![u, w] := by
  have hconst : A = fun _ ↦ A 0 := funext (eq_const_of_apply hA)
  have hAd : DifferentiableAt ℝ A p.1 := by rw [hconst]; exact differentiableAt_const _
  rw [SmoothForm.eval₂_mpullback, mfderiv_gauge_mfderiv_mk, mfderiv_gauge_mfderiv_mk, gauge_mk,
    eval₂_couplingForm_mfderiv_mk_eq_normalCouplingForm hω₀]
  refine normalCouplingForm_normalModelGauge_apply ℓ.differentiableAt hAd
    (differentiableAt_const _) (fun v ↦ ?_) ?_ u w
  · simp [hA, ℓ.fderiv]
  · rw [hconst, ContinuousAlternatingMap.extDeriv_const, ContinuousAlternatingMap.extDeriv_const]

end FlatLine

end TauCeti
