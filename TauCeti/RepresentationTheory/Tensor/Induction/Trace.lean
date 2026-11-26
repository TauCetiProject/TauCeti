/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAction.Orbit.Quotient
public import TauCeti.RepresentationTheory.CharacterTable.ClassFunction
public import TauCeti.RepresentationTheory.Tensor.Induction.Basic

import TauCeti.Data.Setoid.Basic
import TauCeti.GroupTheory.GroupAction.Orbit.Basic
import TauCeti.GroupTheory.QuotientGroup.Basic
import TauCeti.GroupTheory.Perm.WreathProduct.Monomial
import TauCeti.LinearAlgebra.PiTensorProduct.Trace
import TauCeti.RepresentationTheory.Character.Basic

/-!
# Traces and characters of tensor-induced representations

Applying `LinearMap.trace_piTensorProduct_map_comp_reindex` to `Representation.wreathTensor`
expresses the trace of a wreath tensor representation as a product over the cycles of the
underlying permutation. Pulling back along `Subgroup.monomialHom` and telescoping the transversal
words `TauCeti.lWord` via `Subgroup.monomialHom_orbit_prod` gives the trace formula for
`Subgroup.tensorInducedRepresentation`: for any finite-index subgroup `U ≤ G`, any left transversal
`s`, and any representation `ρ` of `U` on a free module over a commutative semiring `R`, the trace
at `g ∈ G` is the product over the `⟨g⟩`-orbits on `G ⧸ U` of the trace of `ρ` at the cycle
monodromy `r⁻¹ * g ^ m * r ∈ U`.

Because `u ↦ LinearMap.trace R M (ρ u)` is invariant under `U`-conjugation, this orbit product
depends only on the `U`-conjugation-invariant function `f : U → R` and not on the transversal `s`,
defining `Subgroup.tensorIndClassFun U f`. For a normal subgroup `H ≤ G`, evaluating
`Subgroup.tensorIndClassFun` at `h ∈ H` expresses the factor product as the values of `f` at
`q.out⁻¹ * h * q.out` for chosen ambient coset representatives in `G ⧸ H` (independent of the choice
of representatives when `f` is `H`-conjugation-invariant).

## Main definitions

* `Subgroup.tensorIndClassFun`: canonical tensor-induced function on `G` attached to a function
  `U → R` for a finite-index subgroup `U ≤ G`.

## Main results

* `Representation.trace_wreathTensor`: trace formula for `Representation.wreathTensor`.
* `Subgroup.tensorIndClassFun_one` and `Subgroup.tensorIndClassFun_mul`: multiplicativity of
  `Subgroup.tensorIndClassFun`.
* `Subgroup.trace_tensorInducedRepresentation` and `Subgroup.character_tensorInducedRepresentation`:
  transversal-independent orbit-product trace and character formulas for
  `Subgroup.tensorInducedRepresentation`.
* `Subgroup.tensorIndClassFun_conj` and `Subgroup.tensorIndClassFun_mem_classFunction`: conjugation
  invariance of `Subgroup.tensorIndClassFun`.
* `Subgroup.tensorIndClassFun_apply_of_mem_of_normal`: evaluation on a normal subgroup.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society 108 (1963), §§2–5.
* J.-P. Serre, *Linear Representations of Finite Groups*, Chapter 7.
-/

public section

open scoped TensorProduct

namespace Representation

/-- **Trace of a wreath tensor product representation.** At `(a, σ)` in the permutation wreath
product `(ι → D) ⋊ Perm ι`, the trace on `⨂[R] _ : ι, M` equals the product over the cycles of `σ`
of the trace of `ρ` at the ordered cycle product of `a`. -/
theorem trace_wreathTensor {R D M : Type*} [CommSemiring R] [Group D]
    [AddCommMonoid M] [Module R M] [Module.Free R M]
    (ρ : Representation R D M) (ι : Type*) [Finite ι] (a : TauCeti.WreathProduct D ι)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers a.right) ι)] :
    LinearMap.trace R (⨂[R] _ : ι, M) (ρ.wreathTensor ι a) =
      ∏ q : MulAction.orbitRel.Quotient (Subgroup.zpowers a.right) ι,
        LinearMap.trace R M
          (ρ (List.ofFn fun t : Fin (Function.minimalPeriod (a.right • ·) q.out) ↦
            a.left ((a.right⁻¹ ^ (t : ℕ)) q.out)).prod) := by
  let := Fintype.ofFinite ι
  rw [wreathTensor_apply, LinearMap.trace_piTensorProduct_map_comp_reindex]
  convert Finset.prod_congr rfl fun q _ ↦ ?_
  congr 1
  rw [map_list_prod, List.map_ofFn]
  rfl

end Representation

namespace Subgroup

/-- **The canonical tensor-induced function of a finite-index subgroup.** For a finite-index
subgroup `U ≤ G` and a function `f : U → R` into a commutative monoid, `U.tensorIndClassFun f g`
is the product over the `⟨g⟩`-orbits on `G ⧸ U` of `f` evaluated at the cycle monodromy
`q.out.out⁻¹ * g ^ m * q.out.out ∈ U`.

When `f` is invariant under `U`-conjugation, `U.tensorIndClassFun f` is invariant under
`G`-conjugation (`Subgroup.tensorIndClassFun_conj`); separately, for any representation `ρ` of `U`
on a free module `M` over a commutative semiring `R`, evaluating at `u ↦ LinearMap.trace R M (ρ u)`
agrees with `LinearMap.trace R _ (U.tensorInducedRepresentation s ρ g)` for every left transversal
`s` (`Subgroup.trace_tensorInducedRepresentation`). -/
noncomputable def tensorIndClassFun {R : Type*} [CommMonoid R] {G : Type*} [Group G]
    (U : Subgroup G) [U.FiniteIndex] (f : U → R) (g : G) : R :=
  letI := U.fintypeQuotientOfFiniteIndex
  letI : Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U)) := Fintype.ofFinite _
  ∏ q : MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U),
    f ⟨q.out.out⁻¹ * g ^ Function.minimalPeriod (g • ·) q.out * q.out.out,
      QuotientGroup.out_conj_pow_minimalPeriod_mem U g q.out⟩

/-- The defining orbit-product formula for `Subgroup.tensorIndClassFun` using any `Fintype`
instance on the `⟨g⟩`-orbits of `G ⧸ U`. -/
theorem tensorIndClassFun_def {R : Type*} [CommMonoid R] {G : Type*} [Group G]
    (U : Subgroup G) [U.FiniteIndex] (f : U → R) (g : G)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U))] :
    U.tensorIndClassFun f g =
      ∏ q : MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U),
        f ⟨q.out.out⁻¹ * g ^ Function.minimalPeriod (g • ·) q.out * q.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem U g q.out⟩ := by
  rw [tensorIndClassFun]
  convert rfl

/-- Tensor induction of the constant `1` function is `1`. -/
@[simp]
theorem tensorIndClassFun_one {R : Type*} [CommMonoid R] {G : Type*} [Group G]
    (U : Subgroup G) [U.FiniteIndex] (g : G) :
    U.tensorIndClassFun (1 : U → R) g = 1 := by
  simp [tensorIndClassFun]

/-- Tensor induction distributes over pointwise products on `U`. -/
@[simp]
theorem tensorIndClassFun_mul {R : Type*} [CommMonoid R] {G : Type*} [Group G]
    (U : Subgroup G) [U.FiniteIndex] (f₁ f₂ : U → R) (g : G) :
    U.tensorIndClassFun (f₁ * f₂) g =
      U.tensorIndClassFun f₁ g * U.tensorIndClassFun f₂ g := by
  simp [tensorIndClassFun, Finset.prod_mul_distrib]

/-- When `f : U → R` is invariant under `U`-conjugation, `Subgroup.tensorIndClassFun U f g` can be
evaluated using any choice of coset representatives `r : G ⧸ U → G`. -/
theorem tensorIndClassFun_eq_prod_of_rep {R : Type*} [CommMonoid R] {G : Type*} [Group G]
    (U : Subgroup G) [U.FiniteIndex] {f : U → R} (hf : ∀ u v : U, f (v * u * v⁻¹) = f u)
    (r : G ⧸ U → G) (hr : ∀ q, (QuotientGroup.mk (r q) : G ⧸ U) = q) (g : G)
    [Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U))] :
    U.tensorIndClassFun f g =
      ∏ q : MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U),
        f ⟨(r q.out)⁻¹ * g ^ Function.minimalPeriod (g • ·) q.out * r q.out,
          conj_pow_minimalPeriod_mem U g (hr q.out)⟩ := by
  rw [tensorIndClassFun_def]
  refine Finset.prod_congr rfl fun q _ ↦ ?_
  exact apply_conj_pow_minimalPeriod_eq_of_orbitRel hf g (MulAction.mem_orbit_self q.out)
    (hr q.out) (QuotientGroup.out_eq' q.out)

/-- **Trace of a tensor-induced representation.** For any finite-index subgroup `U ≤ G`, any left
transversal `s`, and any representation `ρ` of `U` on a free `R`-module `M`, the trace of
`U.tensorInducedRepresentation s ρ g` equals `U.tensorIndClassFun (fun u ↦ trace R M (ρ u)) g`
and in particular does not depend on `s`. -/
theorem trace_tensorInducedRepresentation {R G M : Type*} [CommSemiring R] [Group G]
    (U : Subgroup G) [U.FiniteIndex] (s : U.LeftTransversal)
    [AddCommMonoid M] [Module R M] [Module.Free R M]
    (ρ : Representation R U M) (g : G) :
    LinearMap.trace R (⨂[R] _ : G ⧸ U, M) (U.tensorInducedRepresentation s ρ g) =
      U.tensorIndClassFun (fun u ↦ LinearMap.trace R M (ρ u)) g := by
  let := U.fintypeQuotientOfFiniteIndex
  let := Fintype.ofFinite
    (MulAction.orbitRel.Quotient (Subgroup.zpowers (U.monomialHom s g).right) (G ⧸ U))
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U))
  have hdef : U.tensorInducedRepresentation s ρ g = ρ.wreathTensor (G ⧸ U) (U.monomialHom s g) :=
    LinearMap.ext fun z ↦ Subgroup.tensorInducedRepresentation_apply U s ρ g z
  rw [hdef, Representation.trace_wreathTensor, tensorIndClassFun_eq_prod_of_rep U
    (fun u v ↦ ρ.trace_conj u v) (U.leftTransversalRep s) (U.leftTransversalRep_mk s)]
  let qEquiv : MulAction.orbitRel.Quotient (Subgroup.zpowers (U.monomialHom s g).right) (G ⧸ U) ≃
      MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U) :=
    Quotient.congrRight fun x y ↦ by
      simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      constructor <;> rintro ⟨⟨_, k, rfl⟩, hy⟩
      · refine ⟨⟨g ^ k, k, rfl⟩, ?_⟩
        -- Unfold the `zpowers` subtype action into group powers.
        change g ^ k • y = x
        rwa [Subgroup.smul_def, Equiv.Perm.smul_def, monomialHom_right_zpow] at hy
      · refine ⟨⟨(U.monomialHom s g).right ^ k, k, rfl⟩, ?_⟩
        -- Unfold the `zpowers` subtype action into group powers.
        change g ^ k • y = x at hy
        rwa [Subgroup.smul_def, Equiv.Perm.smul_def, monomialHom_right_zpow]
  refine Fintype.prod_equiv qEquiv _ _ fun q ↦ ?_
  rw [monomialHom_orbit_prod U s g q.out]
  refine apply_conj_pow_minimalPeriod_eq_of_orbitRel
    (f := fun u ↦ LinearMap.trace R M (ρ u)) (fun u v ↦ ρ.trace_conj u v) g ?_
    (U.leftTransversalRep_mk s (qEquiv q).out) (U.leftTransversalRep_mk s q.out)
  exact Setoid.symm' _ (Quotient.rel_out_congrRight_out _ q)

/-- **Character of a tensor-induced representation.** Over any field `k`, the character of
`U.tensorInducedRepresentation s ρ` equals `U.tensorIndClassFun ρ.character`. -/
theorem character_tensorInducedRepresentation {k G V : Type*} [Field k] [Group G]
    (U : Subgroup G) [U.FiniteIndex] (s : U.LeftTransversal)
    [AddCommGroup V] [Module k V]
    (ρ : Representation k U V) :
    (U.tensorInducedRepresentation s ρ).character = U.tensorIndClassFun ρ.character := by
  ext g
  exact trace_tensorInducedRepresentation U s ρ g

private theorem tensorIndClassFun_inv_mul_mul {R G : Type*} [CommMonoid R] [Group G]
    (U : Subgroup G) [U.FiniteIndex] {f : U → R}
    (hf : ∀ u v : U, f (v * u * v⁻¹) = f u) (g r : G) :
    U.tensorIndClassFun f (r⁻¹ * g * r) = U.tensorIndClassFun f g := by
  let := U.fintypeQuotientOfFiniteIndex
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient (Subgroup.zpowers (r⁻¹ * g * r)) (G ⧸ U))
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (G ⧸ U))
  rw [tensorIndClassFun_def, tensorIndClassFun_def]
  exact Fintype.prod_equiv (MulAction.conjOrbitEquiv (α := G ⧸ U) g r) _ _ fun q ↦
    apply_conj_pow_minimalPeriod_conjOrbitEquiv hf Quotient.out QuotientGroup.out_eq' g r q

/-- **Conjugation invariance of `Subgroup.tensorIndClassFun`.** If `f : U → R` is invariant under
`U`-conjugation, then `U.tensorIndClassFun f` is invariant under `G`-conjugation. -/
theorem tensorIndClassFun_conj {R G : Type*} [CommMonoid R] [Group G]
    (U : Subgroup G) [U.FiniteIndex] {f : U → R}
    (hf : ∀ u v : U, f (v * u * v⁻¹) = f u) (g c : G) :
    U.tensorIndClassFun f (c * g * c⁻¹) = U.tensorIndClassFun f g := by
  simpa using tensorIndClassFun_inv_mul_mul U hf g c⁻¹

/-- If `f` is a class function on a finite-index subgroup `U ≤ G`, then `U.tensorIndClassFun f`
is a class function on `G`. -/
theorem tensorIndClassFun_mem_classFunction {k G : Type*} [CommSemiring k] [Group G]
    (U : Subgroup G) [U.FiniteIndex] {f : U → k} (hf : f ∈ TauCeti.ClassFunction k U) :
    U.tensorIndClassFun f ∈ TauCeti.ClassFunction k G := by
  refine TauCeti.ClassFunction.mem_iff.mpr fun g c ↦ ?_
  exact tensorIndClassFun_conj U (fun u v ↦ TauCeti.ClassFunction.mem_iff.mp hf u v) g c

/-- **Normal-subgroup evaluation on `H`.** For a finite-index normal subgroup `H ≤ G` and any
function `f : H → R`, evaluating `H.tensorIndClassFun f` at `h : H` gives the product of `f` over
all coset conjugates `q.out⁻¹ * h * q.out`. -/
theorem tensorIndClassFun_apply_of_mem_of_normal {R G : Type*} [CommMonoid R] [Group G]
    (H : Subgroup G) [H.Normal] [H.FiniteIndex] (f : H → R) (h : H) :
    H.tensorIndClassFun f h =
      letI := H.fintypeQuotientOfFiniteIndex
      ∏ q : G ⧸ H, f (MulAut.conjNormal q.out⁻¹ h) := by
  let := H.fintypeQuotientOfFiniteIndex
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient (Subgroup.zpowers (h : G)) (G ⧸ H))
  rw [tensorIndClassFun_def]
  -- `h ∈ H` fixes every coset, so each `⟨h⟩`-orbit is a single coset, its representative.
  let qEquiv : MulAction.orbitRel.Quotient (Subgroup.zpowers (h : G)) (G ⧸ H) ≃ G ⧸ H :=
    Equiv.ofBijective Quotient.out
      ⟨fun q q' hq ↦ by rw [← Quotient.out_eq' q, ← Quotient.out_eq' q', hq], fun x ↦ by
        refine ⟨Quotient.mk'' x, ?_⟩
        obtain ⟨⟨_, k, rfl⟩, hk⟩ := MulAction.mem_orbit_iff.mp
          (Quotient.mk_out' (s₁ := MulAction.orbitRel (Subgroup.zpowers (h : G)) (G ⧸ H)) x)
        rw [← hk]
        exact TauCeti.smul_quotient_eq_self_of_mem (H.zpow_mem h.property k) x⟩
  refine Fintype.prod_equiv qEquiv _ _ fun q ↦ ?_
  have hper : Function.minimalPeriod (fun x : G ⧸ H ↦ (h : G) • x) q.out = 1 :=
    Function.minimalPeriod_eq_one_iff_isFixedPt.mpr
      (TauCeti.smul_quotient_eq_self_of_mem h.property q.out)
  have hmk : q.out = qEquiv q := (Equiv.ofBijective_apply _ _ q).symm
  have helem :
      (⟨q.out.out⁻¹ * (h : G) ^ Function.minimalPeriod (fun x : G ⧸ H ↦ (h : G) • x) q.out *
          q.out.out, QuotientGroup.out_conj_pow_minimalPeriod_mem H (h : G) q.out⟩ : H) =
        MulAut.conjNormal q.out.out⁻¹ h := by
    apply Subtype.ext
    dsimp only
    rw [hper, pow_one, MulAut.conjNormal_apply, inv_inv]
  rw [helem, ← hmk]

end Subgroup
