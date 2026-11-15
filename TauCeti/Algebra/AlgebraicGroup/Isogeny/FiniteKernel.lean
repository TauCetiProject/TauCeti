/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Kernel
public import TauCeti.RingTheory.Finite.Connected

/-!
# Uniqueness of lifts through homomorphisms with finite kernel

Two homomorphisms from a reduced connected affine group that agree after a homomorphism with
finite scheme-theoretic kernel are equal. This works over every field, including for infinitesimal
kernels and inseparable isogenies. Neither group needs to be of finite type, and the homomorphism
with finite kernel need not be finite, surjective, or central.

In coordinate arrows, `f : H ⟶ K` and `g₁ g₂ : K ⟶ G` satisfy
`f ≫ g₁ = f ≫ g₂`. Their pointwise quotient is a regular map from `Spec G` to the kernel
of `f`. The finite-image constancy theorem `AlgHom.eq_algebraMap_comp_of_moduleFinite` makes
this map constant; its value at the identity is one. Thus uniqueness of lifts through central
isogenies also holds when differentials cannot detect the isogeny.

The kernel map uses `TauCeti.CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff` and the
quotient-point lift. No geometric reducedness or geometric connectedness assumption is needed.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 6 and 21, finite kernels and isogenies.
* T. A. Springer, *Linear Algebraic Groups*, §9.6, simply connected coverings.
-/

public section

open CategoryTheory WithConv

namespace CommHopfAlgCat.Hom

open TauCeti TauCeti.CommHopfAlgCat

universe u v

variable {k : Type u} [Field k] {H K G : CommHopfAlgCat.{v} k}
  [IsReduced G] [ConnectedSpace (PrimeSpectrum G)]

/-- Homomorphism lifts from a reduced connected affine group through a homomorphism with
finite scheme-theoretic kernel are unique, over every field. Coordinate arrows reverse the
group-scheme arrows. The kernel may be nonreduced; no finite-type, surjectivity, or centrality
assumption is imposed. -/
theorem eq_of_comp_eq_of_finite_kernel
    (f : H ⟶ K) [Module.Finite k (K ⧸ (kernelHopfIdeal f).toIdeal)]
    (g₁ g₂ : K ⟶ G) (h : f ≫ g₁ = f ≫ g₂) : g₁ = g₂ := by
  let p : WithConv (K →ₐ[k] G) := toConv g₁.hom.toAlgHom * (toConv g₂.hom.toAlgHom)⁻¹
  have hp : p ∈ quotientPointsSubgroup K (kernelHopfIdeal f) (CommAlgCat.of k G) := by
    apply (mapPointsFunctor_app_eq_one_iff f (CommAlgCat.of k G) p).mp
    rw [← BialgHom.mapDomain_apply]
    have heq : BialgHom.mapDomain (A := G) f.hom (toConv g₁.hom.toAlgHom) =
        BialgHom.mapDomain (A := G) f.hom (toConv g₂.hom.toAlgHom) := by
      apply WithConv.ofConv_injective
      simpa only [BialgHom.mapDomain_apply, ofConv_toConv, CommHopfAlgCat.hom_comp,
        BialgHom.comp_toAlgHom] using congrArg (fun a : H ⟶ G ↦ a.hom.toAlgHom) h
    simp only [p, map_mul, map_inv, heq, mul_inv_cancel]
  let q := (liftQuotientPoint K (kernelHopfIdeal f) (CommAlgCat.of k G) p
    ((mem_quotientPointsSubgroup_iff _ _ _ _).mp hp)).ofConv
  have hq (x : K) : q (Ideal.Quotient.mkₐ k (kernelHopfIdeal f).toIdeal x) = p.ofConv x :=
    liftQuotientPoint_mk K (kernelHopfIdeal f) (CommAlgCat.of k G) p _ x
  have hone : AlgHom.mapValue (Bialgebra.counitAlgHom k G) p = 1 := by
    simp only [p, map_mul, map_inv, AlgHom.mapValue_apply]
    have hc (g : K ⟶ G) :
        (Bialgebra.counitAlgHom k G).comp g.hom.toAlgHom = Bialgebra.counitAlgHom k K :=
      g.hom.counitAlgHom_comp
    simp only [hc, mul_inv_cancel]
  have hpone : p = 1 := by
    apply WithConv.ofConv_injective
    ext x
    have hconstant := AlgHom.congr_fun
      (q.eq_algebraMap_comp_of_moduleFinite (Bialgebra.counitAlgHom k G))
      (Ideal.Quotient.mkₐ k (kernelHopfIdeal f).toIdeal x)
    simp only [AlgHom.comp_apply, Algebra.ofId_apply, hq] at hconstant
    have hc := congrArg (fun a : WithConv (K →ₐ[k] k) ↦ a.ofConv x) hone
    simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
      AlgHom.convOne_apply, Algebra.algebraMap_self, RingHom.id_apply] at hc
    simpa only [hc, AlgHom.convOne_apply] using hconstant
  have heq := mul_inv_eq_one.mp hpone
  apply CommHopfAlgCat.hom_ext
  ext x
  exact AlgHom.congr_fun (WithConv.toConv_injective heq) x

end CommHopfAlgCat.Hom
