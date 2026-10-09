/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Delineation
public import TauCeti.RingTheory.MvPolynomial.IrreducibleBasis

/-!
# Ambient polynomial orders on sectors

On a sector of a polynomial delineation, every member with a nonzero fiber has
nonzero value, hence ambient Taylor order zero. For an irreducible basis whose
fibers are nonzero, the ambient order of each original input on a sector is
therefore exactly the order of its content at the base point. This includes
inputs nullified by vanishing content: their ambient order need not be zero.

Consequently order-invariance of the McCallum projection gives order-invariance
of the original family on every sector. Neither connectedness nor analyticity
is needed for this implication. The order on root sections requires a separate
argument; fiber root multiplicity is not identified with ambient Taylor order.

## References

S. McCallum, *An improved projection operation for cylindrical algebraic
decomposition*, Springer (1998), Sections 2–3 (content and order-invariant lifting).
-/

public section

open MvPolynomial Polynomial Set

namespace TauCeti.Delineation

variable {n : ℕ} {ι : Type*} {P : ι → Polynomial (MvPolynomial (Fin n) ℝ)}
  {S : Set (Fin n → ℝ)}
  (D : Delineation fun i (x : S) ↦ (P i).map (MvPolynomial.eval x.1))

/-- A member with a nonzero fiber has ambient Taylor order zero at every point
of a sector of its delineation. Only nonnullification at that point is needed. -/
theorem orderAt_eq_zero_of_mem_sectorSet (i : ι) {j : Fin (D.count + 1)}
    {a : Fin (n + 1) → ℝ}
    (hi : (P i).map (MvPolynomial.eval (Fin.tail a)) ≠ 0)
    (ha : a ∈ cylinder S '' sectorSet D.root j) :
    ((finSuccEquiv ℝ n).symm (P i)).orderAt a = 0 := by
  obtain ⟨⟨x, t⟩, hx, rfl⟩ := ha
  rw [tail_cylinder] at hi
  apply orderAt_eq_zero_iff.2
  rw [cylinder_def, eval_eq_eval_mv_eval', AlgEquiv.apply_symm_apply]
  exact D.eval_ne_zero_of_mem_sectorSet hi hx

end TauCeti.Delineation

namespace Finset.IsIrreducibleBasis

variable {n : ℕ} [NormalizedGCDMonoid (MvPolynomial (Fin n) ℝ)]
  {F B : Finset (Polynomial (MvPolynomial (Fin n) ℝ))} {S : Set (Fin n → ℝ)}

/-- On a sector of a delineation of the basis, the ambient order of an input
is exactly the order of its content. All basis fibers at the base point are
assumed nonzero; the input itself may be nullified by its content. -/
theorem orderAt_eq_content_of_mem_sectorSet (hB : F.IsIrreducibleBasis B)
    (D : TauCeti.Delineation fun (b : B) (x : S) ↦ b.1.map (MvPolynomial.eval x.1))
    {f : Polynomial (MvPolynomial (Fin n) ℝ)} (hf : f ∈ F)
    {j : Fin (D.count + 1)} {a : Fin (n + 1) → ℝ}
    (hb : ∀ b ∈ B, b.map (MvPolynomial.eval (Fin.tail a)) ≠ 0)
    (ha : a ∈ TauCeti.cylinder S '' TauCeti.sectorSet D.root j) :
    ((finSuccEquiv ℝ n).symm f).orderAt a = f.content.orderAt (Fin.tail a) := by
  obtain ⟨e, he⟩ := hB.exists_orderAt_eq_content_add_sum hf
  rw [he]
  have hz : ∑ b ∈ B, e b • ((finSuccEquiv ℝ n).symm b).orderAt a = 0 := by
    apply Finset.sum_eq_zero
    intro b hmem
    rw [D.orderAt_eq_zero_of_mem_sectorSet ⟨b, hmem⟩ (hb b hmem) ha, smul_zero]
  rw [hz, add_zero]

/-- Constant order of an input's content transfers to constant ambient order
across all sectors of a basis delineation, provided no basis member is nullified.
Vanishing contents and zero inputs are allowed. For McCallum lifting, the content
order hypothesis follows from its membership in the projection. -/
theorem orderAt_eq_of_mem_sectorSet (hB : F.IsIrreducibleBasis B)
    (D : TauCeti.Delineation fun (b : B) (x : S) ↦ b.1.map (MvPolynomial.eval x.1))
    {f : Polynomial (MvPolynomial (Fin n) ℝ)} (hf : f ∈ F)
    (hc : ∀ x ∈ S, ∀ y ∈ S, f.content.orderAt x = f.content.orderAt y)
    (hb : ∀ b ∈ B, ∀ x ∈ S, b.map (MvPolynomial.eval x) ≠ 0)
    {j j' : Fin (D.count + 1)} {a a' : Fin (n + 1) → ℝ}
    (ha : a ∈ TauCeti.cylinder S '' TauCeti.sectorSet D.root j)
    (ha' : a' ∈ TauCeti.cylinder S '' TauCeti.sectorSet D.root j') :
    ((finSuccEquiv ℝ n).symm f).orderAt a = ((finSuccEquiv ℝ n).symm f).orderAt a' := by
  obtain ⟨haS, _⟩ := TauCeti.mem_image_cylinder.mp ha
  obtain ⟨haS', _⟩ := TauCeti.mem_image_cylinder.mp ha'
  rw [hB.orderAt_eq_content_of_mem_sectorSet D hf (fun b hmem ↦ hb b hmem _ haS) ha,
    hB.orderAt_eq_content_of_mem_sectorSet D hf (fun b hmem ↦ hb b hmem _ haS') ha']
  exact hc _ haS _ haS'

end Finset.IsIrreducibleBasis
