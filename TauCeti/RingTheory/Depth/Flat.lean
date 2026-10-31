/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Quotient
public import TauCeti.RingTheory.Depth.Basic
public import TauCeti.RingTheory.Depth.WeaklyRegular
public import TauCeti.RingTheory.Regular.RegularSequence
public import TauCeti.RingTheory.Flat.QuotSMulTop

/-!
# Depth along flat local homomorphisms

Let `R → S` be a local homomorphism of Noetherian local rings, `M` a finite `R`-module and `N` a
finite `S`-module which is flat over `R`. Then the depth of `N ⊗[R] M` over `S` is the depth of
`M` over `R` plus the depth over `S` of the closed fibre `N ⧸ 𝔪_R N`. For `N = S` and `M = R`,
the depth of `S` is the depth of `R` plus the depth of `S ⧸ 𝔪_R S`.

This is the depth half of the dimension and depth formulas for flat local homomorphisms. It is
what makes Cohen–Macaulayness and the conditions `(S_n)` ascend and descend along flat local
homomorphisms with well-behaved closed fibres.

The proof is by induction on the two depths. An `M`-regular element `x ∈ 𝔪_R` stays regular on
the flat module `N ⊗[R] M`, and `N ⊗[R] (M ⧸ x M) = (N ⊗[R] M) ⧸ x (N ⊗[R] M)`. When `M` has depth
zero, an element `y ∈ 𝔪_S` regular on the closed fibre is regular on `N ⊗[R] M`, and `N ⧸ y N` is
again flat over `R` (`Module.Flat.quotSMulTop_of_isSMulRegular_quotient`), with closed fibre
`(N ⧸ 𝔪_R N) ⧸ y (N ⧸ 𝔪_R N)`. When both depths vanish, the residue field of `S` embeds in the
closed fibre, which embeds in `N ⊗[R] M` by flatness, so `N ⊗[R] M` has depth zero.

## Main results

* `IsLocalRing.depth_tensorProduct_eq_add_of_flat`:
  `depth (N ⊗[R] M) = depth M + depth (N ⧸ 𝔪_R N)`.
* `IsLocalRing.depth_eq_add_of_flat`: `depth S = depth R + depth (S ⧸ 𝔪_R S)` for a flat local
  homomorphism `R → S`.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 23.3.
* The Stacks Project, Tag 0337, for the ring version.
-/

public section

universe u u' v

open IsLocalRing TensorProduct Pointwise

namespace IsLocalRing

section Tensor

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {N : Type v} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  {M : Type v} [AddCommGroup M] [Module R M]

/-- If `x ∈ R` kills an `R`-module `P`, its image in `S` kills `N ⊗[R] P`. -/
private theorem smul_tmul_eq_zero_of_smul_eq_zero {P : Type v} [AddCommGroup P] [Module R P]
    {x : R} (hx : ∀ p : P, x • p = 0) (z : N ⊗[R] P) : algebraMap R S x • z = 0 := by
  induction z with
  | add a b ha hb => rw [smul_add, ha, hb, add_zero]
  | tmul n p => rw [algebraMap_smul, ← tmul_smul, hx, tmul_zero]

/-- Dividing `M` by `x` corresponds to dividing `N ⊗[R] M` by the image of `x` in `S`: the map
`N ⊗[R] M → N ⊗[R] (M ⧸ x M)` is surjective with kernel `x (N ⊗[R] M)`. -/
private theorem lTensor_mkQ_eq_zero_iff (x : R) (z : N ⊗[R] M) :
    AlgebraTensorModule.lTensor S N (x • ⊤ : Submodule R M).mkQ z = 0 ↔
      z ∈ (algebraMap R S x • ⊤ : Submodule S (N ⊗[R] M)) := by
  constructor
  · intro hz
    obtain ⟨w, rfl⟩ := ((_root_.lTensor_exact N (LinearMap.exact_subtype_mkQ _)
      (Submodule.mkQ_surjective _)) z).mp hz
    clear hz
    induction w with
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
    | tmul n v =>
      obtain ⟨v, hv⟩ := v
      obtain ⟨m, -, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp hv
      rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, Submodule.coe_mk, tmul_smul,
        ← algebraMap_smul S x]
      exact Submodule.smul_mem_pointwise_smul _ _ _ trivial
  · intro hz
    obtain ⟨z, -, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp hz
    rw [map_smul]
    exact smul_tmul_eq_zero_of_smul_eq_zero
      (Module.mem_annihilator.mp (QuotSMulTop.mem_annihilator M x)) _

/-- The map `N ⊗[R] M → (N ⧸ y N) ⊗[R] M` has kernel `y (N ⊗[R] M)`. -/
private theorem rTensor_mkQ_eq_zero_iff (y : S) (z : N ⊗[R] M) :
    AlgebraTensorModule.rTensor R M (y • ⊤ : Submodule S N).mkQ z = 0 ↔
      z ∈ (y • ⊤ : Submodule S (N ⊗[R] M)) := by
  have hN : LinearMap.range (LinearMap.lsmul S N y) = y • ⊤ := by
    ext n
    simp [Submodule.mem_smul_pointwise_iff_exists]
  have hNM : LinearMap.range (AlgebraTensorModule.rTensor R M (LinearMap.lsmul S N y)) =
      y • ⊤ := by
    have h : ⇑(AlgebraTensorModule.rTensor R M (LinearMap.lsmul S N y)) = (y • ·) :=
      funext fun w ↦ (AlgebraTensorModule.smul_eq_lsmul_rTensor y w).symm
    ext w
    simp [Submodule.mem_smul_pointwise_iff_exists, LinearMap.mem_range, h]
  rw [← LinearMap.mem_ker, ← hN, AlgebraTensorModule.ker_rTensor_mkQ, hNM]

/-- The map `N ⊗[R] M → N ⊗[R] (M ⧸ x M)` is surjective. -/
private theorem lTensor_mkQ_surjective (x : R) :
    Function.Surjective (AlgebraTensorModule.lTensor S N (x • ⊤ : Submodule R M).mkQ) :=
  LinearMap.lTensor_surjective N (Submodule.mkQ_surjective _)

/-- For an ideal `I` of `S`, the map `N ⧸ I N → (N ⧸ y N) ⧸ I (N ⧸ y N)` has kernel
`y (N ⧸ I N)`: both are `N ⧸ (I N + y N)`. -/
private theorem mapQ_mkQ_eq_zero_iff (I : Ideal S) (y : S) (p : N ⧸ (I • ⊤ : Submodule S N)) :
    Submodule.mapQ _ _ (y • ⊤ : Submodule S N).mkQ (Submodule.smul_top_le_comap_smul_top I _) p =
      0 ↔ p ∈ (y • ⊤ : Submodule S (N ⧸ (I • ⊤ : Submodule S N))) := by
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ p
  have hleft : Submodule.Quotient.mk (Submodule.Quotient.mk n : QuotSMulTop y N) =
      (0 : QuotSMulTop y N ⧸ (I • ⊤ : Submodule S (QuotSMulTop y N))) ↔
      n ∈ (I • ⊤ : Submodule S N) ⊔ (y • ⊤ : Submodule S N) := by
    rw [Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, ← Submodule.mem_comap,
      Submodule.comap_smul_top_of_surjective _ _ (Submodule.mkQ_surjective _), Submodule.ker_mkQ]
  rw [Submodule.mapQ_apply, Submodule.mkQ_apply, hleft, ← Submodule.ideal_span_singleton_smul,
    ← Submodule.ideal_span_singleton_smul, ← Submodule.mkQ_apply, ← Submodule.mem_comap,
    Submodule.comap_smul_top_of_surjective _ _ (Submodule.mkQ_surjective _), Submodule.ker_mkQ,
    sup_comm]

/-- The map `N ⧸ I N → (N ⧸ y N) ⧸ I (N ⧸ y N)` is surjective. -/
private theorem mapQ_mkQ_surjective (I : Ideal S) (y : S) :
    Function.Surjective (Submodule.mapQ (I • ⊤ : Submodule S N) _ (y • ⊤ : Submodule S N).mkQ
      (Submodule.smul_top_le_comap_smul_top I _)) := by
  intro q
  obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨Submodule.Quotient.mk n, rfl⟩

end Tensor

section Depth

variable {S : Type u} [CommRing S] [IsLocalRing S] [Small.{v} S]

/-- If `g : P → Q` is a surjective `S`-linear map with kernel `s P`, then `P ⧸ s P` and `Q` have
the same depth. -/
private theorem depth_quotSMulTop_eq_of_surjective {P Q : Type v} [AddCommGroup P] [Module S P]
    [AddCommGroup Q] [Module S Q] {s : S} (g : P →ₗ[S] Q) (hg : Function.Surjective g)
    (hker : ∀ p, g p = 0 ↔ p ∈ (s • ⊤ : Submodule S P)) :
    depth (ModuleCat.of S (QuotSMulTop s P)) = depth (ModuleCat.of S Q) :=
  depth_eq_of_linearEquiv <| (Submodule.quotEquivOfEq _ _ <| by ext p; exact (hker p).symm).trans
    (g.quotKerEquivOfSurjective hg)

variable [IsNoetherianRing S]

/-- Over a Noetherian local ring, a finite module and an element of the maximal ideal regular on
it: the depth of the module is one more than the depth of the quotient. A restatement of
`IsLocalRing.depth_quotSMulTop_succ_eq_depth` with the quotient replaced by an isomorphic module
`Q`, presented as the target of a surjection with kernel `s P`. -/
private theorem depth_eq_add_one_of_surjective {P Q : Type v} [AddCommGroup P] [Module S P]
    [Module.Finite S P] [AddCommGroup Q] [Module S Q] {s : S} (hs : s ∈ maximalIdeal S)
    (reg : IsSMulRegular P s) (g : P →ₗ[S] Q) (hg : Function.Surjective g)
    (hker : ∀ p, g p = 0 ↔ p ∈ (s • ⊤ : Submodule S P)) :
    depth (ModuleCat.of S P) = depth (ModuleCat.of S Q) + 1 := by
  rw [← depth_quotSMulTop_eq_of_surjective g hg hker, depth_quotSMulTop_succ_eq_depth reg hs]

section Flat

variable {R : Type u'} [CommRing R] [Algebra R S] [IsLocalRing R] [IsNoetherianRing R]
  [IsLocalHom (algebraMap R S)] [Small.{v} R]
  {N : Type v} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  {M : Type v} [AddCommGroup M] [Module R M]

omit [IsNoetherianRing S] [Small.{v} S] [IsNoetherianRing R] [Small.{v} R] [Module R N]
  [IsScalarTower R S N] in
/-- If the closed fibre `N ⧸ 𝔪_R N` of a finite `S`-module vanishes, so does `N`. -/
private theorem subsingleton_of_subsingleton_quotient [Module.Finite S N]
    (h : Subsingleton (N ⧸ ((maximalIdeal R).map (algebraMap R S) • ⊤ : Submodule S N))) :
    Subsingleton N := by
  by_contra hN
  rw [not_subsingleton_iff_nontrivial] at hN
  rw [Submodule.Quotient.subsingleton_iff] at h
  exact Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
    ((map_maximalIdeal_le _).trans (maximalIdeal_le_jacobson _)) h.symm

omit [IsNoetherianRing S] [IsNoetherianRing R] [IsLocalHom (algebraMap R S)] in
/-- If `M` and the closed fibre `N ⧸ 𝔪_R N` have depth zero, so does `N ⊗[R] M`: the residue field
of `S` embeds in the closed fibre `N ⊗[R] κ(R)`, which embeds in `N ⊗[R] M` by flatness. -/
private theorem depth_tensorProduct_eq_zero [Module.Flat R N]
    (hM : depth (ModuleCat.of R M) = 0)
    (hN : depth (ModuleCat.of S (N ⧸ ((maximalIdeal R).map (algebraMap R S) • ⊤ :
      Submodule S N))) = 0) :
    depth (ModuleCat.of S (N ⊗[R] M)) = 0 := by
  rw [depth_eq_zero_iff_nontrivial_linearMap] at hM hN ⊢
  obtain ⟨f, hf⟩ := exists_ne (0 : R ⧸ maximalIdeal R →ₗ[R] M)
  obtain ⟨g, hg⟩ := exists_ne (0 : S ⧸ maximalIdeal S →ₗ[S]
    N ⧸ ((maximalIdeal R).map (algebraMap R S) • ⊤ : Submodule S N))
  have : IsSimpleModule R (R ⧸ maximalIdeal R) :=
    isSimpleModule_iff_quot_maximal.2 ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
  have hfi : Function.Injective f := f.injective_or_eq_zero.resolve_right hf
  let e := AlgebraTensorModule.tensorQuotEquivQuotMapSMul (S := S) (N := N) (maximalIdeal R)
  let h := AlgebraTensorModule.lTensor S N f ∘ₗ e.symm.toLinearMap
  have hh : Function.Injective h :=
    (Module.Flat.lTensor_preserves_injective_linearMap f hfi).comp e.symm.injective
  refine nontrivial_of_ne (h ∘ₗ g) 0 fun H ↦ hg (LinearMap.ext fun q ↦ hh ?_)
  simpa using LinearMap.congr_fun H q

/-- When `M` has depth zero, the depth of `N ⊗[R] M` is that of the closed fibre of `N`. The
induction on the depth of the closed fibre divides `N` by an element of `𝔪_S` regular on it. -/
private theorem depth_tensorProduct_eq_of_depth_eq_zero [Module.Finite R M]
    (hM : depth (ModuleCat.of R M) = 0) (e : ℕ) :
    ∀ (N : Type v) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
      [Module.Finite S N] [Module.Flat R N],
      depth (ModuleCat.of S (N ⧸ ((maximalIdeal R).map (algebraMap R S) • ⊤ :
        Submodule S N))) = e →
      depth (ModuleCat.of S (N ⊗[R] M)) = e := by
  induction e with
  | zero => exact fun N _ _ _ _ _ _ hN ↦ depth_tensorProduct_eq_zero hM hN
  | succ e ih =>
    intro N _ _ _ _ _ _ hN
    obtain ⟨y, hy, reg⟩ := exists_isSMulRegular_of_depth_ne_zero (R := S) <| by
      rw [hN]
      exact_mod_cast e.succ_ne_zero
    have := Module.Flat.quotSMulTop_of_isSMulRegular_quotient reg
    have : Module.Finite S (N ⊗[R] M) := .equiv (AlgebraTensorModule.cancelBaseChange R S S N M)
    have hfib := depth_eq_add_one_of_surjective hy reg _ (mapQ_mkQ_surjective _ y)
      (mapQ_mkQ_eq_zero_iff _ y)
    rw [hN, Nat.cast_succ] at hfib
    rw [depth_eq_add_one_of_surjective hy
      (Module.Flat.isSMulRegular_tensorProduct_of_isSMulRegular_quotient reg M) _
      (AlgebraTensorModule.rTensor_mkQ_surjective _) (rTensor_mkQ_eq_zero_iff y),
      ih (QuotSMulTop y N) (ENat.add_left_injective_of_ne_top ENat.one_ne_top hfib).symm,
      Nat.cast_succ]

/-- The depth formula when both depths are finite, by induction on the depth of `M`, dividing `M`
by an element of `𝔪_R` regular on it. -/
private theorem depth_tensorProduct_eq_add_of_eq [Module.Finite S N] [Module.Flat R N] {e : ℕ}
    (hN : depth (ModuleCat.of S (N ⧸ ((maximalIdeal R).map (algebraMap R S) • ⊤ :
      Submodule S N))) = e) (d : ℕ) :
    ∀ (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
      depth (ModuleCat.of R M) = d → depth (ModuleCat.of S (N ⊗[R] M)) = d + e := by
  induction d with
  | zero =>
    intro M _ _ _ hM
    rw [Nat.cast_zero, zero_add]
    exact depth_tensorProduct_eq_of_depth_eq_zero hM e N hN
  | succ d ih =>
    intro M _ _ _ hM
    obtain ⟨x, hx, reg⟩ := exists_isSMulRegular_of_depth_ne_zero (R := R) <| by
      rw [hM]
      exact_mod_cast d.succ_ne_zero
    have hM' := depth_quotSMulTop_succ_eq_depth reg hx
    rw [hM, Nat.cast_succ] at hM'
    have : Module.Finite S (N ⊗[R] M) := .equiv (AlgebraTensorModule.cancelBaseChange R S S N M)
    rw [depth_eq_add_one_of_surjective (map_maximalIdeal_le _ (Ideal.mem_map_of_mem _ hx))
      (isSMulRegular_algebraMap_iff S |>.mpr (reg.lTensor N)) _ (lTensor_mkQ_surjective x)
      (lTensor_mkQ_eq_zero_iff x),
      ih (QuotSMulTop x M) (ENat.add_left_injective_of_ne_top ENat.one_ne_top hM'),
      Nat.cast_succ, add_right_comm]

/-- **Depth along a flat local homomorphism.** Let `R → S` be a local homomorphism of Noetherian
local rings, `M` a finite `R`-module and `N` a finite `S`-module which is flat over `R`. Then the
depth of `N ⊗[R] M` over `S` is the depth of `M` over `R` plus the depth over `S` of the closed
fibre `N ⧸ 𝔪_R N`. -/
theorem depth_tensorProduct_eq_add_of_flat [Module.Finite S N] [Module.Flat R N]
    [Module.Finite R M] :
    depth (ModuleCat.of S (N ⊗[R] M)) = depth (ModuleCat.of R M) +
      depth (ModuleCat.of S (N ⧸ ((maximalIdeal R).map (algebraMap R S) • ⊤ :
        Submodule S N))) := by
  have : Module.Finite S (N ⊗[R] M) := .equiv (AlgebraTensorModule.cancelBaseChange R S S N M)
  rcases subsingleton_or_nontrivial
    (N ⧸ ((maximalIdeal R).map (algebraMap R S) • ⊤ : Submodule S N)) with hN | hN
  · have := subsingleton_of_subsingleton_quotient hN
    rw [depth_eq_top_of_subsingleton (ModuleCat.of S (N ⊗[R] M)),
      depth_eq_top_of_subsingleton (ModuleCat.of S
        (N ⧸ ((maximalIdeal R).map (algebraMap R S) • ⊤ : Submodule S N))), add_top]
  rcases subsingleton_or_nontrivial M with hM | hM
  · rw [depth_eq_top_of_subsingleton (ModuleCat.of S (N ⊗[R] M)),
      depth_eq_top_of_subsingleton (ModuleCat.of R M), top_add]
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp
    ((depth_eq_top_iff (ModuleCat.of R M)).not.mpr (not_subsingleton M))
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp
    ((depth_eq_top_iff (ModuleCat.of S
      (N ⧸ ((maximalIdeal R).map (algebraMap R S) • ⊤ : Submodule S N)))).not.mpr
      (not_subsingleton _))
  rw [← hd, ← he]
  exact depth_tensorProduct_eq_add_of_eq he.symm d M hd.symm

end Flat

end Depth

/-- **Depth along a flat local homomorphism of rings.** For a flat local homomorphism `R → S` of
Noetherian local rings, the depth of `S` is the depth of `R` plus the depth of the closed fibre
`S ⧸ 𝔪_R S`, as a module over `S`. -/
@[stacks 0337]
theorem depth_eq_add_of_flat {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S] :
    depth (ModuleCat.of S S) = depth (ModuleCat.of R R) +
      depth (ModuleCat.of S (S ⧸ (maximalIdeal R).map (algebraMap R S))) := by
  have h := depth_tensorProduct_eq_add_of_flat (R := R) (S := S) (N := S) (M := R)
  rwa [depth_eq_of_linearEquiv (AlgebraTensorModule.rid R S S),
    depth_eq_of_linearEquiv (Submodule.quotEquivOfEq _ _ (by simp) :
      (S ⧸ ((maximalIdeal R).map (algebraMap R S) • ⊤ : Submodule S S)) ≃ₗ[S]
        (S ⧸ (maximalIdeal R).map (algebraMap R S)))] at h

end IsLocalRing
