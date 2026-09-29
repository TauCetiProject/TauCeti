/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.Basic
import Mathlib.RingTheory.Flat.Equalizer
import TauCeti.Algebra.HopfAlgebra.Antipode
import TauCeti.LinearAlgebra.TensorProduct.Intersection

/-!
# Coinvariants of a Hopf ideal

Let `H` be a commutative Hopf algebra over `R` and let `I` be a Hopf ideal, cutting out a closed
subgroup `N` of the affine group `G` represented by `H`. The **coinvariants** of `I` are the
elements `h` with

```text
(id ⊗ π) (Δ h) = h ⊗ 1   in H ⊗[R] (H ⧸ I),
```

where `π : H → H ⧸ I` is the quotient map. Equivalently `Δ h - h ⊗ 1 ∈ H ⊗ I`. They form a
subalgebra `H^{co H/I}` of `H`: geometrically, the functions `f` on `G` that are invariant under
right translation by `N`, `f (g n) = f g`. Over a field, when `N` is normal, this subalgebra is the
coordinate ring of the quotient `G / N` (Waterhouse, §16.3; Takeuchi); that identification, which
rests on faithful flatness of `H` over its Hopf subalgebras, is not proved here. The coinvariants
are therefore the candidate representing object for the fppf quotient sheaf
`TauCeti.CommHopfAlgCat.fppfQuotientSheaf`.

This file sets up that candidate and proves its Hopf-algebraic closure properties:

* the functor-of-points characterization: `h` is a coinvariant exactly when
  `(g * n)(h) = g(h)` for all points `g` of `G` and `n` of `N` over every value algebra;
* every coinvariant is congruent to its counit modulo `I`, so the augmentation ideal of the
  coinvariants is contained in `I`: `N` lies in the kernel of `G → G / N`;
* the coinvariants of the zero ideal are the scalars and those of the augmentation ideal are
  everything;
* when `H` is flat, comultiplication maps the coinvariants into `H ⊗ H^{co H/I}`, so they form a
  left coideal subalgebra;
* when `I` is normal, the antipode preserves the coinvariants, and comultiplication maps them into
  `H^{co H/I} ⊗ H^{co H/I}` as soon as `H` and `H ⧸ H^{co H/I}` are flat (for instance over a
  field). So the coinvariants of a normal Hopf ideal are a Hopf subalgebra.

## Main declarations

* `TauCeti.HopfIdeal.coinvariants`: the subalgebra of right `N`-invariant functions.
* `TauCeti.HopfIdeal.mem_coinvariants_iff` and
  `TauCeti.HopfIdeal.mem_coinvariants_iff_comul_sub_mem_rightTensorIdeal`: membership criteria.
* `TauCeti.HopfIdeal.ofConv_mul_apply_of_mem_coinvariants` and
  `TauCeti.HopfIdeal.mem_coinvariants_iff_forall_mul`: the functor-of-points characterization.
* `TauCeti.HopfIdeal.sub_algebraMap_counit_mem_of_mem_coinvariants`: coinvariants are constant on
  `N`.
* `TauCeti.HopfIdeal.coinvariants_mono`, `TauCeti.HopfIdeal.coinvariants_bot` and
  `TauCeti.HopfIdeal.coinvariants_augmentation`: dependence on the Hopf ideal.
* `TauCeti.HopfIdeal.comul_mem_range_lTensor_of_mem_coinvariants`: the left coideal property.
* `TauCeti.HopfIdeal.IsNormal.antipode_mem_coinvariants`: stability under the antipode.
* `TauCeti.HopfIdeal.IsNormal.comul_mem_range_rTensor_of_mem_coinvariants`: the right coideal
  property for a normal Hopf ideal.
* `TauCeti.HopfIdeal.IsNormal.coinvariantsSubcoalgebra`: the coinvariants of a normal Hopf ideal
  as a subcoalgebra.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §16.3.
* M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*, Manuscripta Math.
  **7** (1972), 251–270.
* J. S. Milne, *Algebraic Groups* (2017), §5.c.
-/

public section

open scoped TensorProduct
open CategoryTheory WithConv

namespace TauCeti

universe u v w

namespace HopfIdeal

section Basic

variable {R : Type u} {H : Type v} [CommSemiring R] [CommRing H] [HopfAlgebra R H]

/-- The **coinvariants** of a Hopf ideal `I`: the elements `h` with `(id ⊗ π) (Δ h) = h ⊗ 1`,
where `π : H → H ⧸ I` is the quotient map. Geometrically these are the functions on the affine
group that are invariant under right translation by the closed subgroup cut out by `I`. -/
noncomputable def coinvariants (I : HopfIdeal R H) : Subalgebra R H :=
  AlgHom.equalizer
    ((Algebra.TensorProduct.map (AlgHom.id R H) (Ideal.Quotient.mkₐ R I.toIdeal)).comp
      (Bialgebra.comulAlgHom R H))
    Algebra.TensorProduct.includeLeft

variable {I : HopfIdeal R H} {h : H}

/-- Membership in the coinvariants: `(id ⊗ π) (Δ h) = h ⊗ 1`. -/
@[simp]
theorem mem_coinvariants_iff :
    h ∈ I.coinvariants ↔
      Algebra.TensorProduct.map (AlgHom.id R H) (Ideal.Quotient.mkₐ R I.toIdeal)
          (Coalgebra.comul (R := R) h) = h ⊗ₜ[R] (1 : H ⧸ I.toIdeal) :=
  AlgHom.mem_equalizer _ _ h

/-- A coinvariant is congruent modulo `I` to the scalar given by its counit: the functions
invariant under the subgroup cut out by `I` are constant on that subgroup. -/
theorem mk_eq_algebraMap_counit_of_mem_coinvariants (hh : h ∈ I.coinvariants) :
    Ideal.Quotient.mk I.toIdeal h = algebraMap R (H ⧸ I.toIdeal) (Coalgebra.counit (R := R) h) := by
  -- Apply `ε ⊗ id` to the defining equation `(id ⊗ π) (Δ h) = h ⊗ 1`.
  let e : H ⊗[R] (H ⧸ I.toIdeal) →ₗ[R] H ⧸ I.toIdeal :=
    (TensorProduct.lid R _).toLinearMap ∘ₗ (Coalgebra.counit (R := R) (A := H)).rTensor _
  have hlhs : e (Algebra.TensorProduct.map (AlgHom.id R H) (Ideal.Quotient.mkₐ R I.toIdeal)
      (Coalgebra.comul (R := R) h)) = Ideal.Quotient.mk I.toIdeal h := by
    have hcomm : e ∘ₗ (Algebra.TensorProduct.map (AlgHom.id R H)
        (Ideal.Quotient.mkₐ R I.toIdeal)).toLinearMap =
        (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap ∘ₗ (TensorProduct.lid R H).toLinearMap ∘ₗ
          (Coalgebra.counit (R := R) (A := H)).rTensor H := by
      ext a b
      simp [e, Algebra.smul_def]
    have := LinearMap.congr_fun hcomm (Coalgebra.comul (R := R) h)
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe,
      Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul] at this
    rw [this, Ideal.Quotient.mkₐ_eq_mk]
  have hrhs : e (h ⊗ₜ[R] (1 : H ⧸ I.toIdeal)) =
      algebraMap R (H ⧸ I.toIdeal) (Coalgebra.counit (R := R) h) := by
    simp [e, Algebra.smul_def]
  rw [← hlhs, mem_coinvariants_iff.mp hh, hrhs]

/-- Enlarging the Hopf ideal shrinks the subgroup it cuts out, so enlarges the coinvariants. -/
theorem coinvariants_mono {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    I.coinvariants ≤ J.coinvariants := by
  intro h hh
  let φ := Ideal.Quotient.factorₐ R (toIdeal_le_toIdeal.mpr hIJ)
  have hfactor := congrArg (Algebra.TensorProduct.map (AlgHom.id R H) φ)
    (mem_coinvariants_iff.mp hh)
  have hcomp := AlgHom.congr_fun (Algebra.TensorProduct.map_comp (AlgHom.id R H) (AlgHom.id R H)
    φ (Ideal.Quotient.mkₐ R I.toIdeal)) (Coalgebra.comul (R := R) h)
  rw [AlgHom.id_comp, Ideal.Quotient.factorₐ_comp_mk, AlgHom.comp_apply] at hcomp
  rw [mem_coinvariants_iff, hcomp, hfactor, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    map_one]

end Basic

section Ring

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable {I : HopfIdeal R H} {h : H}

/-- Membership in the coinvariants: `Δ h - h ⊗ 1` lies in `H ⊗ I`. -/
theorem mem_coinvariants_iff_comul_sub_mem_rightTensorIdeal :
    h ∈ I.coinvariants ↔
      Coalgebra.comul (R := R) h - h ⊗ₜ[R] (1 : H) ∈
        rightTensorIdeal (R := R) (H := H) I.toIdeal := by
  rw [← ker_tensorProduct_map_id_quotient, RingHom.mem_ker, mem_coinvariants_iff]
  simp [sub_eq_zero]

/-- A coinvariant minus its counit lies in the Hopf ideal: the augmentation ideal of the
coinvariants is contained in `I`. -/
theorem sub_algebraMap_counit_mem_of_mem_coinvariants (hh : h ∈ I.coinvariants) :
    h - algebraMap R H (Coalgebra.counit (R := R) h) ∈ I := by
  rw [← mem_toIdeal, ← Ideal.Quotient.eq, mk_eq_algebraMap_counit_of_mem_coinvariants hh,
    Ideal.Quotient.mk_algebraMap]

/-- The zero Hopf ideal cuts out the whole group, whose right-invariant functions are the
constants. -/
@[simp]
theorem coinvariants_bot : (⊥ : HopfIdeal R H).coinvariants = ⊥ := by
  refine eq_bot_iff.mpr fun h hh ↦ Algebra.mem_bot.mpr ⟨Coalgebra.counit (R := R) h, ?_⟩
  exact (sub_eq_zero.mp (mem_bot.mp (sub_algebraMap_counit_mem_of_mem_coinvariants hh))).symm

/-- **Coinvariants form a left coideal.** Over a flat Hopf algebra, comultiplication maps the
coinvariants of `I` into `H ⊗ H^{co H/I}`: if `f` is right `N`-invariant then so is
`y ↦ f (x y)` for every `x`. -/
theorem comul_mem_range_lTensor_of_mem_coinvariants [Module.Flat R H] (hh : h ∈ I.coinvariants) :
    Coalgebra.comul (R := R) h ∈
      LinearMap.range ((Subalgebra.toSubmodule I.coinvariants).subtype.lTensor H) := by
  let Q := H ⧸ I.toIdeal
  let π : H →ₗ[R] Q := (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap
  let f : H →ₗ[R] H ⊗[R] Q := π.lTensor H ∘ₗ Coalgebra.comul
  let g : H →ₗ[R] H ⊗[R] Q := (TensorProduct.mk R H Q).flip 1
  have hmap (y : H ⊗[R] H) :
      Algebra.TensorProduct.map (AlgHom.id R H) (Ideal.Quotient.mkₐ R I.toIdeal) y =
        π.lTensor H y := by
    induction y with
    | tmul a b => simp [π]
    | add y z hy hz => simp [hy, hz]
  have hB : Subalgebra.toSubmodule I.coinvariants = LinearMap.eqLocus f g := by
    ext x
    simp [mem_coinvariants_iff, hmap, f, g]
  -- Both `id ⊗ f` and `id ⊗ g` send `Δ h` to the reassociation of `Δ h ⊗ 1`.
  have hf : f.lTensor H (Coalgebra.comul (R := R) h) =
      TensorProduct.assoc R H H Q (Coalgebra.comul (R := R) h ⊗ₜ[R] 1) := by
    have hswap := LinearMap.congr_fun
      ((LinearMap.lTensor_comp_rTensor (f := Coalgebra.comul (R := R) (A := H)) (g := π)).trans
        (LinearMap.rTensor_comp_lTensor (f := Coalgebra.comul (R := R) (A := H)) (g := π)).symm)
      (Coalgebra.comul (R := R) h)
    have hassoc := LinearMap.congr_fun (LinearMap.lTensor_tensor (M := H) (N := H) π)
      ((Coalgebra.comul (R := R) (A := H)).rTensor H (Coalgebra.comul (R := R) h))
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hswap hassoc
    rw [LinearMap.lTensor_comp_apply, ← Coalgebra.coassoc_apply,
      ← LinearEquiv.apply_symm_apply (TensorProduct.assoc R H H Q)
        (π.lTensor H |>.lTensor H _), ← hassoc, hswap, ← hmap, mem_coinvariants_iff.mp hh,
      LinearMap.rTensor_tmul]
  have hg (y : H ⊗[R] H) : g.lTensor H y = TensorProduct.assoc R H H Q (y ⊗ₜ[R] 1) := by
    induction y with
    | tmul a b => simp [g]
    | add y z hy hz => simp [hy, hz, TensorProduct.add_tmul]
  have hmem : Coalgebra.comul (R := R) h ∈ LinearMap.eqLocus
      (TensorProduct.AlgebraTensorModule.lTensor R H f)
      (TensorProduct.AlgebraTensorModule.lTensor R H g) := by
    rw [LinearMap.mem_eqLocus, TensorProduct.AlgebraTensorModule.coe_lTensor,
      TensorProduct.AlgebraTensorModule.coe_lTensor, hf, hg]
  rw [Module.Flat.eqLocus_lTensor_eq] at hmem
  obtain ⟨y, hy⟩ := hmem
  rw [hB]
  exact ⟨y, by rw [← hy, TensorProduct.AlgebraTensorModule.coe_lTensor]⟩

end Ring

section Points

variable {R : Type u} [CommRing R] {H : _root_.CommHopfAlgCat.{v} R} {I : HopfIdeal R H} {h : H}

/-- Evaluating the product of two points `g` and `n` of the affine group factors through the
quotient map when `n` belongs to the subgroup cut out by `I`: it is the product map of `g` and the
factored point applied to `(id ⊗ π) (Δ h)`. -/
private theorem ofConv_mul_apply_eq_lift {A : CommAlgCat.{w} R}
    (g : HopfAlgebra.points (R := R) (H := H) A) (n : HopfAlgebra.points (R := R) (H := H) A)
    (n' : H ⧸ I.toIdeal →ₐ[R] A) (hn : n.ofConv = n'.comp (Ideal.Quotient.mkₐ R I.toIdeal))
    (x : H) :
    (g * n).ofConv x = Algebra.TensorProduct.lift g.ofConv n' (fun _ _ ↦ .all _ _)
      (Algebra.TensorProduct.map (AlgHom.id R H) (Ideal.Quotient.mkₐ R I.toIdeal)
        (Coalgebra.comul (R := R) x)) := by
  rw [← AlgHom.comp_apply]
  have hcomp : (Algebra.TensorProduct.lift g.ofConv n' fun _ _ ↦ .all _ _).comp
      (Algebra.TensorProduct.map (AlgHom.id R H) (Ideal.Quotient.mkₐ R I.toIdeal)) =
      Algebra.TensorProduct.lift g.ofConv n.ofConv fun _ _ ↦ .all _ _ := by
    rw [hn]
    ext <;> simp
  rw [hcomp]
  exact AlgHom.convMul_apply g n x

/-- A coinvariant is invariant under right translation by the points of the subgroup cut out by
`I`: `(g * n)(h) = g(h)`. -/
theorem ofConv_mul_apply_of_mem_coinvariants (hh : h ∈ I.coinvariants) {A : CommAlgCat.{w} R}
    (g : HopfAlgebra.points (R := R) (H := H) A) {n : HopfAlgebra.points (R := R) (H := H) A}
    (hn : n ∈ CommHopfAlgCat.quotientPointsSubgroup H I A) :
    (g * n).ofConv h = g.ofConv h := by
  obtain ⟨n', rfl⟩ := hn
  rw [ofConv_mul_apply_eq_lift g _ n'.ofConv
      (AlgHom.ext fun x ↦ CommHopfAlgCat.quotientPointsHom_apply_apply H I A n' x),
    mem_coinvariants_iff.mp hh, Algebra.TensorProduct.lift_tmul, map_one, mul_one]

/-- **Functor-of-points characterization of the coinvariants.** An element is a coinvariant
exactly when it is invariant under right translation by the points of the subgroup cut out by
`I`, over every commutative value algebra. -/
theorem mem_coinvariants_iff_forall_mul :
    h ∈ I.coinvariants ↔
      ∀ (A : CommAlgCat.{v} R) (g n : HopfAlgebra.points (R := R) (H := H) A),
        n ∈ CommHopfAlgCat.quotientPointsSubgroup H I A → (g * n).ofConv h = g.ofConv h := by
  refine ⟨fun hh A g n hn ↦ ofConv_mul_apply_of_mem_coinvariants hh g hn, fun hmul ↦ ?_⟩
  -- Test against the two canonical points of `H ⊗ (H ⧸ I)`.
  let A : CommAlgCat.{v} R := CommAlgCat.of R (H ⊗[R] (H ⧸ I.toIdeal))
  let n' : H ⧸ I.toIdeal →ₐ[R] A := Algebra.TensorProduct.includeRight
  have hlift : Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft : H →ₐ[R] A) n'
      (fun _ _ ↦ .all _ _) = AlgHom.id R A :=
    Algebra.TensorProduct.lift_includeLeft_includeRight
  have key := hmul A (toConv Algebra.TensorProduct.includeLeft)
    (CommHopfAlgCat.quotientPointsHom H I A (toConv n'))
    (CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup H I A _)
  rw [ofConv_mul_apply_eq_lift _ _ n'
      (AlgHom.ext fun x ↦ CommHopfAlgCat.quotientPointsHom_apply_apply H I A _ x),
    ofConv_toConv, hlift, AlgHom.id_apply] at key
  exact mem_coinvariants_iff.mpr key

/-- The augmentation ideal cuts out the trivial subgroup, so every function is invariant. -/
@[simp]
theorem coinvariants_augmentation : (augmentation R H).coinvariants = ⊤ := by
  refine eq_top_iff.mpr fun h _ ↦ mem_coinvariants_iff_forall_mul.mpr fun A g n hn ↦ ?_
  rw [(CommHopfAlgCat.mem_quotientPointsSubgroup_augmentation_iff H A n).mp hn, mul_one]

/-- **The antipode preserves the coinvariants of a normal Hopf ideal.** If `f` is invariant under
right translation by a normal subgroup `N`, so is `g ↦ f (g⁻¹)`, because
`(g n)⁻¹ = g⁻¹ (g n⁻¹ g⁻¹)` and `g n⁻¹ g⁻¹ ∈ N`. -/
theorem IsNormal.antipode_mem_coinvariants (hI : I.IsNormal) (hh : h ∈ I.coinvariants) :
    HopfAlgebraStruct.antipode R h ∈ I.coinvariants := by
  rw [mem_coinvariants_iff_forall_mul]
  intro A g n hn
  have hconj : g * n⁻¹ * g⁻¹ ∈ CommHopfAlgCat.quotientPointsSubgroup H I A :=
    (CommHopfAlgCat.quotientPointsSubgroup_normal H I hI A).conj_mem _ (inv_mem hn) g
  calc (g * n).ofConv (HopfAlgebraStruct.antipode R h)
      _ = ((g * n)⁻¹).ofConv h := (AlgHom.convInv_apply _ h).symm
      _ = (g⁻¹ * (g * n⁻¹ * g⁻¹)).ofConv h := by
        simp only [mul_inv_rev, ← mul_assoc, inv_mul_cancel, one_mul]
      _ = (g⁻¹).ofConv h := ofConv_mul_apply_of_mem_coinvariants hh _ hconj
      _ = g.ofConv (HopfAlgebraStruct.antipode R h) := AlgHom.convInv_apply _ h

/-- **Coinvariants of a normal Hopf ideal form a right coideal.** Over a flat Hopf algebra,
comultiplication maps the coinvariants of a normal Hopf ideal into `H^{co H/I} ⊗ H`. -/
theorem IsNormal.comul_mem_range_rTensor_of_mem_coinvariants [Module.Flat R H] (hI : I.IsNormal)
    (hh : h ∈ I.coinvariants) :
    Coalgebra.comul (R := R) h ∈
      LinearMap.range ((Subalgebra.toSubmodule I.coinvariants).subtype.rTensor H) := by
  -- Apply the left coideal property to `S h` and transport it back along
  -- `Δ ∘ S = (S ⊗ S) ∘ τ ∘ Δ` and `S ∘ S = id`.
  let B := Subalgebra.toSubmodule I.coinvariants
  let S : H →ₗ[R] H := HopfAlgebraStruct.antipode R
  let SB : B →ₗ[R] B := S.restrict fun _ hx ↦ hI.antipode_mem_coinvariants hx
  obtain ⟨y, hy⟩ := comul_mem_range_lTensor_of_mem_coinvariants (hI.antipode_mem_coinvariants hh)
  have hcomm : TensorProduct.map S S ∘ₗ (TensorProduct.comm R H H).toLinearMap ∘ₗ
      B.subtype.lTensor H = B.subtype.rTensor H ∘ₗ TensorProduct.map SB S ∘ₗ
        (TensorProduct.comm R H B).toLinearMap := by
    ext a b
    simp [SB, S]
  refine ⟨TensorProduct.map SB S (TensorProduct.comm R H B y), ?_⟩
  have := LinearMap.congr_fun hcomm y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at this
  rw [← this, hy, ← TauCeti.HopfAlgebra.antipode_comul_antidistrib_apply,
    TauCeti.HopfAlgebra.antipode_antipode]

/-- **The coinvariants of a normal Hopf ideal form a subcoalgebra**, when `H` and
`H ⧸ H^{co H/I}` are flat, for instance over a field. Together with
`TauCeti.HopfIdeal.IsNormal.antipode_mem_coinvariants`, this makes the coinvariants a Hopf
subalgebra of `H`. -/
noncomputable def IsNormal.coinvariantsSubcoalgebra [Module.Flat R H]
    [Module.Flat R (H ⧸ Subalgebra.toSubmodule I.coinvariants)] (hI : I.IsNormal) :
    Subcoalgebra R H :=
  Subcoalgebra.ofSubmodule (Subalgebra.toSubmodule I.coinvariants) fun _ hc ↦ by
    rw [Submodule.range_map_subtype_subtype]
    exact ⟨comul_mem_range_lTensor_of_mem_coinvariants hc,
      hI.comul_mem_range_rTensor_of_mem_coinvariants hc⟩

/-- The subcoalgebra of coinvariants has the coinvariants as its elements. -/
@[simp]
theorem IsNormal.mem_coinvariantsSubcoalgebra [Module.Flat R H]
    [Module.Flat R (H ⧸ Subalgebra.toSubmodule I.coinvariants)] (hI : I.IsNormal) :
    h ∈ hI.coinvariantsSubcoalgebra ↔ h ∈ I.coinvariants := by
  rw [IsNormal.coinvariantsSubcoalgebra, Subcoalgebra.mem_ofSubmodule,
    Subalgebra.mem_toSubmodule]

end Points

end HopfIdeal

end TauCeti
