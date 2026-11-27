/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.Representation
public import TauCeti.RepresentationTheory.OfMulAction.Hecke.Level

/-!
# The right action of a double coset through the Hecke sum

Let `U` be a subgroup of a group `G` (in practice a compact open subgroup of a locally profinite
group), `A` a commutative ring and `ρ` a representation of `G` on `V`. For a `U`-invariant vector
`v`, the linear map `q_v : A[G] → V`, `δ_x ↦ ρ(x)⁻¹ v` (`TauCeti.HeckeAlgebraLevel.heckeTestMap`),
is `U`-invariant for the left regular representation of `G` on `A[G]`. For a double coset
`D = U g U`, the Hecke sum `HeckeCoset.heckeSum D (leftRegular) q_v` of the double-coset Hecke
ring, evaluated on `δ_1`, is `∑ᵢ ρ(aᵢ)⁻¹ v` over representatives of the right cosets
`U g U = ⊔ᵢ U aᵢ`. This is the right action `v * [UgU]` of the basis element `[UgU]` of the
Hecke algebra of level `U` (the indicator of the orbit of `(U, gU)`,
`TauCeti.HeckeAlgebraLevel.rightAction`), whose explicit form is the sum of `ρ(t.out) v` over the
left cosets `t` with `(t, U)` in the orbit of `(U, gU)`; the inverses `t.out⁻¹` of these
representatives represent the right cosets of `U g U`.

## Main definitions

* `TauCeti.HeckeAlgebraLevel.heckeTestMap ρ v`: the map `δ_x ↦ ρ(x)⁻¹ v` on `A[G]`.

## Main results

* `TauCeti.HeckeAlgebraLevel.heckeTestMap_comp_leftRegular_of_mem`: `q_v` is `U`-invariant.
* `TauCeti.HeckeAlgebraLevel.heckeTestMap_apply_intertwiningMap`: `q_v` is natural in `V`.
* `TauCeti.HeckeAlgebraLevel.heckeSum_heckeTestMap_single_one`: the Hecke sum of `q_v` at `δ_1`
  is `v * [UgU]`.

## References

* D. Treumann and A. Venkatesh, *Functoriality, Smith theory, and the Brauer homomorphism*,
  Ann. of Math. 183 (2016), §2.10, (2.10.1)–(2.10.3), pp. 187–188 (arXiv:1407.2346v1 §2.10).
-/

public section
noncomputable section

open MulAction Representation DoubleCoset

open scoped Pointwise

namespace TauCeti

namespace HeckeAlgebraLevel

variable {G : Type*} [Group G] {U : Subgroup G} {A : Type*} [CommRing A]
  {V : Type*} [AddCommGroup V] [Module A V] (ρ : Representation A G V)

/-- The linear map `q_v : A[G] → V`, `δ_x ↦ ρ(x)⁻¹ v`. -/
def heckeTestMap (v : V) : MonoidAlgebra A G →ₗ[A] V :=
  Finsupp.linearCombination A (fun x ↦ ρ x⁻¹ v) ∘ₗ (MonoidAlgebra.coeffLinearEquiv A).toLinearMap

@[simp]
theorem heckeTestMap_single (v : V) (x : G) (c : A) :
    heckeTestMap ρ v (MonoidAlgebra.single x c) = c • ρ x⁻¹ v := by
  simp [heckeTestMap]

/-- **`q_v` is `U`-invariant** for the left regular representation, for `v` a `U`-invariant
vector. -/
theorem heckeTestMap_comp_leftRegular_of_mem {v : V} (hv : v ∈ invariants (ρ.comp U.subtype))
    {u : G} (hu : u ∈ U) : heckeTestMap ρ v ∘ₗ leftRegular A G u = heckeTestMap ρ v := by
  refine MonoidAlgebra.lhom_ext' fun x ↦ LinearMap.ext_ring ?_
  have hv' : ρ u⁻¹ v = v := hv ⟨u⁻¹, inv_mem hu⟩
  simp [mul_inv_rev, hv']

/-- `q_v` is natural in the representation: an intertwining map `f` sends `q_v` to `q_{f v}`. -/
theorem heckeTestMap_apply_intertwiningMap {W : Type*} [AddCommGroup W] [Module A W]
    {σ : Representation A G W} (f : IntertwiningMap ρ σ) (v : V) :
    heckeTestMap σ (f v) = f.toLinearMap ∘ₗ heckeTestMap ρ v := by
  refine MonoidAlgebra.lhom_ext' fun x ↦ LinearMap.ext_ring ?_
  simp [f.isIntertwining]

omit [CommRing A] in
/-- `(yU, U)` lies in the orbit of `(U, gU)` exactly when `y⁻¹ ∈ U g U`. -/
theorem mem_orbit_iff_inv_mem_doubleCoset (g y : G) :
    ((y : G ⧸ U), ((1 : G) : G ⧸ U)) ∈ orbit G (((1 : G) : G ⧸ U), (g : G ⧸ U)) ↔
      y⁻¹ ∈ doubleCoset g U U := by
  simp only [mem_orbit_iff, Prod.smul_mk, Quotient.smul_mk, smul_eq_mul, mul_one, Prod.mk.injEq,
    QuotientGroup.eq, mem_doubleCoset]
  constructor
  · rintro ⟨k, hky, hkg⟩
    refine ⟨(k⁻¹ * y)⁻¹, inv_mem hky, (k * g)⁻¹, ?_, by group⟩
    simpa using hkg
  · rintro ⟨a, ha, b, hb, hy⟩
    refine ⟨b⁻¹ * g⁻¹, ?_, ?_⟩
    · rw [← inv_inv y, hy]
      simpa [mul_assoc] using inv_mem ha
    · simpa [mul_assoc] using hb

omit [CommRing A] in
/-- If `S` is the set of left cosets `t` with `t.out⁻¹ ∈ U g U`, the inverses `t.out⁻¹` represent
the right cosets of `U g U`. -/
private theorem doubleCoset_eq_iUnion_op_out_inv_smul (g : G) (S : Finset (G ⧸ U))
    (hS : ∀ t : G ⧸ U, t ∈ S ↔ (t.out⁻¹ : G) ∈ doubleCoset g U U) :
    doubleCoset g U U = ⋃ t : S, MulOpposite.op (((t : G ⧸ U).out)⁻¹ : G) • (U : Set G) := by
  ext x
  simp only [Set.mem_iUnion, mem_rightCoset_iff, inv_inv, SetLike.mem_coe]
  constructor
  · intro hx
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U x⁻¹
    refine ⟨⟨((x⁻¹ : G) : G ⧸ U), (hS _).2 ?_⟩, ?_⟩
    · obtain ⟨a, ha, b, hb, hab⟩ := mem_doubleCoset.1 hx
      refine mem_doubleCoset.2 ⟨(u : G)⁻¹ * a, mul_mem (inv_mem u.property) ha, b, hb, ?_⟩
      rw [hu, hab]
      group
    · simp only [hu, mul_inv_cancel_left]
      exact u.property
  · rintro ⟨⟨t, ht⟩, hxt⟩
    obtain ⟨a, ha, b, hb, hab⟩ := mem_doubleCoset.1 ((hS t).1 ht)
    refine mem_doubleCoset.2 ⟨x * t.out * a, mul_mem hxt ha, b, hb, ?_⟩
    have hx : x = x * t.out * (t.out)⁻¹ := by group
    rw [hab] at hx
    simpa [mul_assoc] using hx

omit [CommRing A] in
/-- Distinct left cosets `t` give distinct right cosets `U t.out⁻¹`. -/
private theorem injective_op_out_inv_smul (S : Finset (G ⧸ U)) :
    Function.Injective fun t : S ↦ MulOpposite.op (((t : G ⧸ U).out)⁻¹ : G) • (U : Set G) := by
  intro t s hts
  have h := (rightCoset_eq_iff U).1 hts
  rw [inv_inv] at h
  apply Subtype.ext
  rw [← QuotientGroup.out_eq' (t : G ⧸ U), ← QuotientGroup.out_eq' (s : G ⧸ U)]
  exact (QuotientGroup.eq.2 h).symm

variable [FiniteStabilizerOrbits G (G ⧸ U)]

/-- **The Hecke sum of `q_v` is the right action of the double coset.** For a double coset
`D = U g U` and a `U`-invariant `v`, the Hecke sum `∑ᵢ q_v ∘ λ(aᵢ)` over the right cosets
`U g U = ⊔ᵢ U aᵢ`, evaluated on `δ_1`, is `v * [UgU]`, the right action of the indicator of the
orbit of `(U, gU)`. -/
theorem heckeSum_heckeTestMap_single_one (D : HeckeCoset (⊤ : Submonoid G) U U)
    [Finite (DecompQuotient U U (D.out : G)⁻¹)] (v : invariants (ρ.comp U.subtype)) :
    HeckeCoset.heckeSum D ((leftRegular A G).comp (⊤ : Submonoid G).subtype)
        (Submonoid.mem_top _) le_top (heckeTestMap ρ v) (MonoidAlgebra.single 1 1) =
      (rightAction ρ (MulOpposite.op ⟨_, PermutationHecke.indicator_orbit_mem
        (((1 : G) : G ⧸ U), ((D.out : G) : G ⧸ U))⟩) v : V) := by
  classical
  set g : G := (D.out : G)
  have hfin := FiniteStabilizerOrbits.finite_setOf_mk_left_eq (G := G) ((1 : G) : G ⧸ U)
    (Quotient.mk _ (((1 : G) : G ⧸ U), (g : G ⧸ U)))
  set S := hfin.toFinset
  have hS (t : G ⧸ U) : t ∈ S ↔ (t.out⁻¹ : G) ∈ doubleCoset g U U := by
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Quotient.eq, orbitRel_apply,
      ← mem_orbit_iff_inv_mem_doubleCoset, QuotientGroup.out_eq']
  rw [HeckeCoset.heckeSum_eq_sum_of_rightCosets D _ _ _ le_top
    (fun γ hγ ↦ heckeTestMap_comp_leftRegular_of_mem ρ v.property hγ)
    (fun t : S ↦ ((t : G ⧸ U).out)⁻¹) (fun _ ↦ Submonoid.mem_top _)
    (doubleCoset_eq_iUnion_op_out_inv_smul g S hS) (injective_op_out_inv_smul S)]
  -- The column of `[UgU]` at `U` is supported on `S`, where it is `1`.
  have hsub : (PermutationHecke.column (⟨_, PermutationHecke.indicator_orbit_mem
      (((1 : G) : G ⧸ U), (g : G ⧸ U))⟩ : HeckeAlgebraLevel G U A)
      ((1 : G) : G ⧸ U)).support ⊆ S := by
    intro t ht
    rw [Finsupp.mem_support_iff, PermutationHecke.column_apply] at ht
    have ht' := Set.mem_of_indicator_ne_zero ht
    rw [← QuotientGroup.out_eq' t, mem_orbit_iff_inv_mem_doubleCoset] at ht'
    exact (hS t).2 ht'
  rw [LinearMap.sum_apply, coe_rightAction_apply,
    Finsupp.sum_of_support_subset _ hsub (fun t c ↦ c • ρ t.out (v : V)) fun _ _ ↦ zero_smul _ _,
    ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  have hmem : ((t : G ⧸ U), ((1 : G) : G ⧸ U)) ∈
      orbit G (((1 : G) : G ⧸ U), (g : G ⧸ U)) := by
    rw [← QuotientGroup.out_eq' (t : G ⧸ U), mem_orbit_iff_inv_mem_doubleCoset]
    exact (hS _).1 t.property
  simp [Set.indicator_of_mem hmem]

end HeckeAlgebraLevel

end TauCeti
