/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TriangleGroup.PermutationRepresentation
public import TauCeti.Combinatorics.PermutationTriple.Regular

/-!
# Regular triples and normal subgroups of triangle groups

A permutation triple `t` of degree `n` whose components have orders dividing `a`, `b`, `c` is a
permutation representation `TauCeti.TriangleGroup.toPerm t : Δ(a, b, c) →* Equiv.Perm (Fin n)`.
The preimage of the stabilizer of a sheet `i` is the point stabilizer of this action.

This file proves the *normality criterion*: for a connected triple, the point stabilizer is a
normal subgroup of `Δ(a, b, c)` exactly when the triple is regular. In that case the point
stabilizer is the kernel of the representation, a normal subgroup whose index is the degree
`n`, the order of the monodromy group.

## Main results

* `TauCeti.TriangleGroup.normal_comap_stabilizer_toPerm_iff`: for a connected triple, the point
  stabilizer of its representation is normal exactly when the triple is regular.
* `TauCeti.TriangleGroup.comap_stabilizer_toPerm_eq_ker`: when the monodromy group acts freely
  (e.g. for a regular triple), the point stabilizer of every sheet is the kernel of the
  representation.
* `TauCeti.TriangleGroup.index_ker_toPerm`: the kernel of the representation has index the order
  of the monodromy group, and `TauCeti.TriangleGroup.index_ker_toPerm_of_isRegular`: for a
  regular triple this is the degree.

## References

* E. Girondo, G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins d'Enfants*,
  LMS Student Texts 79, Cambridge University Press, 2012, Definition 2.64 and Proposition 2.66.
* G. A. Jones, D. Singerman, *Belyi functions, hypermaps and Galois groups*, Bull. London Math.
  Soc. 28 (1996), 561–590.
-/

open Equiv

public section

namespace TauCeti

namespace TriangleGroup

variable {a b c n : ℕ} (t : PermutationTriple n) (ha : t.σ0 ^ a = 1) (hb : t.σ1 ^ b = 1)
  (hc : t.σinf ^ c = 1)

/-- The representation of a connected triple is transitive on the sheets. -/
private theorem exists_toPerm_apply_eq (ht : t.IsConnected) (i k : Fin n) :
    ∃ κ : TriangleGroup a b c, toPerm t ha hb hc κ i = k := by
  obtain ⟨g, hg⟩ := ht.isPretransitive.exists_smul_eq i k
  obtain ⟨κ, hκ⟩ : (g : Perm (Fin n)) ∈ (toPerm t ha hb hc).range :=
    (range_toPerm t ha hb hc).symm ▸ g.2
  exact ⟨κ, hκ ▸ hg⟩

/-- For a triple whose monodromy group acts freely (for instance a regular triple), the point
stabilizer of every sheet under the representation of the triangle group is the kernel of the
representation. -/
theorem comap_stabilizer_toPerm_eq_ker [IsCancelSMul t.monodromyGroup (Fin n)] (i : Fin n) :
    (MulAction.stabilizer (Perm (Fin n)) i).comap (toPerm t ha hb hc) =
      (toPerm t ha hb hc).ker := by
  ext δ
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MonoidHom.mem_ker]
  refine ⟨fun hδ => ?_, fun hδ => by rw [hδ, one_smul]⟩
  have hmem : toPerm t ha hb hc δ ∈ t.monodromyGroup :=
    range_toPerm t ha hb hc ▸ MonoidHom.mem_range.mpr ⟨δ, rfl⟩
  exact congrArg Subtype.val
    (IsCancelSMul.eq_one_of_smul (g := (⟨_, hmem⟩ : t.monodromyGroup)) (x := i) hδ)

/-- **The normality criterion.** For a connected triple, the point stabilizer of a sheet under the
representation of the triangle group is a normal subgroup exactly when the triple is regular. -/
theorem normal_comap_stabilizer_toPerm_iff (ht : t.IsConnected) (i : Fin n) :
    ((MulAction.stabilizer (Perm (Fin n)) i).comap (toPerm t ha hb hc)).Normal ↔ t.IsRegular := by
  refine ⟨fun hN => ?_, fun hreg => ?_⟩
  · set K := (MulAction.stabilizer (Perm (Fin n)) i).comap (toPerm t ha hb hc)
    -- All point stabilizers are conjugate to `K`, hence equal to it.
    have hK : ∀ (δ : TriangleGroup a b c) (k : Fin n), toPerm t ha hb hc δ k = k ↔ δ ∈ K := by
      intro δ k
      obtain ⟨κ, hκ⟩ := exists_toPerm_apply_eq t ha hb hc ht i k
      have hconj : κ⁻¹ * δ * κ ∈ K ↔ toPerm t ha hb hc δ k = k := by
        rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, map_mul, map_mul, map_inv,
          Perm.smul_def, Perm.mul_apply, Perm.mul_apply, hκ, Perm.inv_eq_iff_eq, hκ]
      rw [← hconj]
      exact ⟨fun h => by simpa [mul_assoc] using hN.conj_mem _ h κ,
        fun h => by simpa using hN.conj_mem _ h κ⁻¹⟩
    have : IsCancelSMul t.monodromyGroup (Fin n) := by
      refine isCancelSMul_iff_stabilizer_eq_bot.mpr fun j => ?_
      refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => ?_
      obtain ⟨δ, hδ⟩ : (g : Perm (Fin n)) ∈ (toPerm t ha hb hc).range :=
        (range_toPerm t ha hb hc).symm ▸ g.2
      have hδj : toPerm t ha hb hc δ j = j := hδ ▸ hg
      refine Subtype.ext <| hδ ▸ Equiv.ext fun k => ?_
      exact (hK δ k).mpr ((hK δ j).mp hδj)
    exact ht.isRegular
  · have := hreg.isCancelSMul
    rw [comap_stabilizer_toPerm_eq_ker t ha hb hc i]
    infer_instance

/-- The kernel of the representation of a triple has index the order of its monodromy group, the
image of the representation. -/
theorem index_ker_toPerm : (toPerm t ha hb hc).ker.index = Nat.card t.monodromyGroup := by
  rw [Subgroup.index_ker, range_toPerm]

/-- The kernel of the representation of a regular triple has index the degree. -/
theorem index_ker_toPerm_of_isRegular (ht : t.IsRegular) : (toPerm t ha hb hc).ker.index = n :=
  (index_ker_toPerm t ha hb hc).trans (PermutationTriple.isRegular_iff_card_monodromyGroup.mp ht).2

end TriangleGroup

end TauCeti
