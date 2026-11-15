/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

import Mathlib.GroupTheory.OrderOfElement
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import TauCeti.RepresentationTheory.Invariants

/-!
# Low-degree group cohomology

For a trivial representation `A` of a group `G`, Mathlib identifies `H¹(G, A)` with the group of
additive homomorphisms `G →+ A`. This file records the consequence that `H¹(G, A)` vanishes when
`G` is finite and `A` has no additive torsion, since a homomorphism from a finite group into a
torsion-free group is zero.

It also records the `H¹` criterion for taking invariants to preserve a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. The general result for `G`-invariants follows from the degree-zero
part of Mathlib's long exact cohomology sequence. The result for a normal subgroup `S` applies it
to the restricted sequence and retains the quotient-group action.

Finally, it records an identity satisfied by a `2`-cocycle `f` of a monoid along two adjacent
commuting squares `d * a' = a * d₁` and `d₁ * b' = b * d₂`: three instances of the cocycle law
express `d • f (a', b')` through the values of `f` at the sides and diagonals of the squares.
It also records that a `2`-cocycle of a group `G` vanishing on `G × N` and on `N × G`, for a normal
subgroup `N`, is constant on the cosets of `N` in both variables and takes `N`-fixed values: the
input for descending such a cocycle to `G ⧸ N`. Summing the identity along the squares over a finite
normal subgroup `N` shows that the norm of `N` multiplies a `2`-cocycle by the order of `N` up to an
explicit coboundary.

## Main statements

* `TauCeti.groupCohomology.isZero_H1_of_isTrivial`: `H¹(G, A) = 0` for a trivial representation `A`
  of a finite group `G` without additive torsion.
* `TauCeti.groupCohomology.shortExact_map_invariantsFunctor`: taking `G`-invariants preserves a
  short exact sequence when `H¹(G, X₁) = 0`.
* `TauCeti.groupCohomology.shortExact_map_quotientToInvariantsFunctor`: taking `S`-invariants
  preserves a short exact sequence whose kernel `X₁` has `H¹(S, X₁) = 0`.
* `Rep.h2Representative`: a chosen two-cocycle representing a class in `H²`.
* `TauCeti.groupCohomology.smul_map_eq_of_isCocycle₂_of_mul_eq_mul`: the `2`-cocycle identity
  along two adjacent commuting squares.
* `TauCeti.groupCohomology.apply_mul_snd_of_isCocycle₂_of_vanishing`,
  `apply_mul_fst_of_isCocycle₂_of_vanishing` and `smul_apply_of_isCocycle₂_of_vanishing`: a
  `2`-cocycle vanishing on `G × N` and on `N × G` is constant on the cosets of `N` in both
  variables and takes `N`-fixed values.
* `TauCeti.groupCohomology.sum_smul_apply_of_isCocycle₂`: the norm of a finite normal subgroup `N`
  multiplies a `2`-cocycle by `#N` up to a coboundary.
-/

public noncomputable section

universe u

open CategoryTheory Limits Rep

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

/-- A chosen two-cocycle representing `u ∈ H²(G, A)`. -/
def h2Representative (A : Rep k G) (u : groupCohomology A 2) :
    groupCohomology.cocycles₂ A :=
  Classical.choose ((ModuleCat.epi_iff_surjective (groupCohomology.H2π A)).mp inferInstance u)

/-- The chosen two-cocycle represents the original second-cohomology class. -/
@[simp]
theorem H2π_h2Representative (A : Rep k G) (u : groupCohomology A 2) :
    groupCohomology.H2π A (h2Representative A u) = u :=
  Classical.choose_spec
    ((ModuleCat.epi_iff_surjective (groupCohomology.H2π A)).mp inferInstance u)

end Rep

namespace TauCeti.groupCohomology

open _root_.groupCohomology

variable {k G : Type u} [CommRing k] [Group G]

/-- `H¹(G, A) = 0` for a trivial representation `A` of a finite group `G` whose underlying module
has no additive torsion. -/
theorem isZero_H1_of_isTrivial [Finite G] (A : Rep k G) [A.IsTrivial] [IsAddTorsionFree A] :
    IsZero (groupCohomology A 1) :=
  -- `H¹(G, A)` is `Hom(G, A)`, and a homomorphism from a finite group to a torsion-free group
  -- vanishes
  have : Subsingleton (Additive G →+ A) := subsingleton_of_forall_eq 0 fun f ↦
    AddMonoidHom.ext fun g ↦ (f.isOfFinAddOrder (isOfFinAddOrder_of_finite g)).eq_zero'
  (ModuleCat.isZero_of_subsingleton (ModuleCat.of k (Additive G →+ A))).of_iso <|
    H1IsoOfIsTrivial A

variable (k G) in
/-- Taking invariants preserves a short exact sequence of `G`-representations when the first
cohomology of its kernel vanishes. -/
theorem shortExact_map_invariantsFunctor {X : ShortComplex (Rep k G)}
    (hX : X.ShortExact) (h1 : IsZero (groupCohomology X.X₁ 1)) :
    (X.map (invariantsFunctor k G)).ShortExact := by
  have h0 : (X.map (functor k G 0)).ShortExact := by
    refine { exact := mapShortComplex₂_exact hX 0, mono_f := ?_, epi_g := ?_ }
    · -- The first map of `X.map (functor k G 0)` unfolds to the degree-zero
      -- cohomology map; rewriting `functor_map` alone does not unfold the
      -- mapped short complex's `f` projection.
      change Mono (map (MonoidHom.id G) X.f 0)
      exact @mono_map_0_of_mono _ _ _ _ _ _ X.f hX.mono_f
    · exact (mapShortComplex₃_exact hX (i := 0) (j := 1) rfl).epi_f
        (h1.eq_of_tgt _ _)
  exact ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (H0Iso X.X₁) (H0Iso X.X₂) (H0Iso X.X₃)
      (by exact (map_id_comp_H0Iso_hom X.f).symm)
      (by exact (map_id_comp_H0Iso_hom X.g).symm)) h0

variable (S : Subgroup G) [S.Normal]

/-- If `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is short exact and `H¹(S, X₁) = 0`, then taking `S`-invariants
preserves short exactness as a sequence of representations of `G ⧸ S`. -/
theorem shortExact_map_quotientToInvariantsFunctor {X : ShortComplex (Rep k G)}
    (hX : X.ShortExact) (h1 : IsZero (groupCohomology (res S.subtype X.X₁) 1)) :
    (X.map (quotientToInvariantsFunctor k S)).ShortExact := by
  have hXS : (X.map (resFunctor S.subtype)).ShortExact :=
    (Rep.shortExact_res S.subtype).2 hX
  have h := shortExact_map_invariantsFunctor k S hXS h1
  exact (CategoryTheory.ShortExact.reflects_shortExact_of_faithful
    (forget₂ (Rep k (G ⧸ S)) (ModuleCat k))) (by
      -- After forgetting the quotient action, the object and maps of
      -- `quotientToInvariantsFunctor` unfold to invariants of the restriction;
      -- rewriting functor composition alone does not identify these fields.
      change ((X.map (resFunctor S.subtype)).map (invariantsFunctor k S)).ShortExact
      exact h)

section IsCocycle₂

variable {K A : Type*} [Monoid K] [AddCommGroup A] [MulAction K A]

/-- A `2`-cocycle identity along two adjacent commuting squares: if `d * a' = a * d₁` and
`d₁ * b' = b * d₂` in a monoid `K`, then for a `2`-cocycle `f : K × K → A`, `d • f (a', b')` is an
alternating sum of the values of `f` at the sides of the two squares and at the products `a' * b'`
and `a * b`. -/
theorem smul_map_eq_of_isCocycle₂_of_mul_eq_mul {f : K × K → A} (hf : IsCocycle₂ f)
    {d a' b' a b d₁ d₂ : K} (h₁ : d * a' = a * d₁) (h₂ : d₁ * b' = b * d₂) :
    d • f (a', b') = a • f (d₁, b') - a • f (b, d₂) - f (d, a' * b') + f (a * b, d₂) +
      f (d, a') - f (a, d₁) + f (a, b) := by
  -- The cocycle law at `(d, a', b')`, `(a, d₁, b')` and `(a, b, d₂)`, matched along `h₁`, `h₂`.
  have e1 := hf d a' b'
  have e2 := hf a d₁ b'
  rw [h₁] at e1
  rw [h₂] at e2
  linear_combination (norm := abel) -e1 + e2 - hf a b d₂

/-- A `2`-cocycle of a monoid `K` vanishing on `K × N`, for a subset `N`, is unchanged by right
multiplication of its second argument by `N`. -/
theorem apply_mul_snd_of_isCocycle₂_of_vanishing {K A : Type*} [Monoid K] [AddCommGroup A]
    [DistribMulAction K A] {N : Set K} {f : K × K → A} (hf : IsCocycle₂ f)
    (hR : ∀ (g : K) (n : N), f (g, n) = 0) (g h : K) (n : N) : f (g, h * n) = f (g, h) := by
  simpa [hR] using (hf g h n).symm

section Vanishing

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A] {N : Subgroup G}

/-- A `2`-cocycle vanishing on `G × N` and on `N × G`, for a normal subgroup `N`, is unchanged by
right multiplication of its first argument by `N`. -/
theorem apply_mul_fst_of_isCocycle₂_of_vanishing [N.Normal] {f : G × G → A} (hf : IsCocycle₂ f)
    (hR : ∀ (g : G) (n : N), f (g, n) = 0) (hL : ∀ (n : N) (g : G), f (n, g) = 0) (g h : G)
    (n : N) : f (g * n, h) = f (g, h) := by
  have h₁ := hf g n h
  -- `n * h = h * (h⁻¹ * n * h)`, with `h⁻¹ * n * h ∈ N` by normality.
  have h₂ := apply_mul_snd_of_isCocycle₂_of_vanishing hf hR g h
    ⟨_, ‹N.Normal›.conj_mem' _ n.2 h⟩
  rw [← mul_assoc, mul_inv_cancel_left] at h₂
  rw [hR, hL, smul_zero, zero_add, add_zero] at h₁
  rw [h₁, h₂]

/-- The values of a `2`-cocycle vanishing on `G × N` and on `N × G`, for a normal subgroup `N`, are
fixed by `N`. -/
theorem smul_apply_of_isCocycle₂_of_vanishing [N.Normal] {f : G × G → A} (hf : IsCocycle₂ f)
    (hR : ∀ (g : G) (n : N), f (g, n) = 0) (hL : ∀ (n : N) (g : G), f (n, g) = 0) (n : N)
    (g h : G) : (n : G) • f (g, h) = f (g, h) := by
  have h₁ := hf n g h
  -- `n * g = g * (g⁻¹ * n * g)`, with `g⁻¹ * n * g ∈ N` by normality.
  have h₂ := apply_mul_fst_of_isCocycle₂_of_vanishing hf hR hL g h
    ⟨_, ‹N.Normal›.conj_mem' _ n.2 g⟩
  rw [← mul_assoc, mul_inv_cancel_left] at h₂
  rw [hL, hL, add_zero, add_zero, h₂] at h₁
  exact h₁.symm

end Vanishing

section Norm

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A] (N : Subgroup G)
  [N.Normal] [Fintype N]

/-- The norm of a finite normal subgroup `N` multiplies a `2`-cocycle `f` by the order of `N` up
to a coboundary: `∑ n : N, n • f (g, h) = #N • f (g, h) + (g • b h - b (g * h) + b g)` for
`b k = ∑ n : N, (f (n, k) - f (k, n))`. -/
theorem sum_smul_apply_of_isCocycle₂ {f : G × G → A} (hf : IsCocycle₂ f) (g h : G) :
    ∑ n : N, (n : G) • f (g, h) = Nat.card N • f (g, h) +
      (g • ∑ n : N, (f (n, h) - f (h, n)) - ∑ n : N, (f (n, g * h) - f (g * h, n)) +
        ∑ n : N, (f (n, g) - f (g, n))) := by
  -- Conjugation by `g⁻¹` and by `(g * h)⁻¹` permute `N`.
  have e₁ (F : G → A) : ∑ n : N, F (MulAut.conjNormal g⁻¹ n) = ∑ n : N, F n :=
    Fintype.sum_equiv (MulAut.conjNormal g⁻¹).toEquiv _ _ fun _ ↦ rfl
  have e₂ (F : G → A) : ∑ n : N, F (MulAut.conjNormal (g * h)⁻¹ n) = ∑ n : N, F n :=
    Fintype.sum_equiv (MulAut.conjNormal (g * h)⁻¹).toEquiv _ _ fun _ ↦ rfl
  -- The cocycle law along the squares `n * g = g * n₁` and `n₁ * h = h * n₂`, for the conjugates
  -- `n₁ = g⁻¹ * n * g` and `n₂ = (g * h)⁻¹ * n * (g * h)` of `n`.
  have key (n : N) := smul_map_eq_of_isCocycle₂_of_mul_eq_mul hf
    (d := n) (a' := g) (b' := h) (a := g) (b := h)
    (d₁ := MulAut.conjNormal g⁻¹ n) (d₂ := MulAut.conjNormal (g * h)⁻¹ n)
    (by simp [mul_assoc]) (by simp [mul_assoc])
  rw [Finset.sum_congr rfl fun n _ ↦ key n]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, ← Finset.smul_sum, smul_sub]
  rw [e₁ fun x ↦ f (x, h), e₂ fun x ↦ f (h, x), e₂ fun x ↦ f (g * h, x), e₁ fun x ↦ f (g, x)]
  abel

end Norm

end IsCocycle₂

end TauCeti.groupCohomology
