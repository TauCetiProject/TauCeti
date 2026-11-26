/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Defect.Class
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.Basic

/-!
# Defect groups from a defect class

Let `k` be a field of characteristic `p`, `G` a finite group, `e_B` a block idempotent of `k[G]`
and `λ_B : Z(k[G]) → k` a `k`-algebra homomorphism with `λ_B(e_B) = 1`, the central character of
the block. For a defect class `C` of `B` (`TauCeti.IsDefectClass`) and `x ∈ C`, the defect groups
of `B` are exactly the Sylow `p`-subgroups of the centralizers `C_G(x)`, `x ∈ C` (Martínez,
Definition 3.2 and Theorem 4.3, pp. 17 and 24, over an algebraically closed field).

The proof uses relative traces only. Let `S` be a Sylow `p`-subgroup of `C_G(x)`.

* `Br_S(e_B) ≠ 0`: since `x` centralizes `S`, the coefficient of `Br_S(e_B)` at `x` is the
  coefficient `a_B(C)` of `e_B` at `x`, which is nonzero.
* `e_B ∈ Tr_S^G(k[G]^S)`: the class sum is `K_C = Tr_{C_G(x)}^G(x)`, and
  `Tr_S^G(k[G]^S) = Tr_{C_G(x)}^G(k[G]^{C_G(x)})` since `|C_G(x) : S|` is prime to `p`. As
  `Z(k[G]) e_B` is local and `λ_B(K_C) ≠ 0`, `K_C e_B` is invertible in it, so `e_B` is a multiple
  of `K_C`.

So `S` is a `p`-subgroup with `Br_S(e_B) ≠ 0`, and every `p`-subgroup `Q ≥ S` with
`Br_Q(e_B) ≠ 0` lies in a conjugate of `S` (`TauCeti.eq_of_le_of_mem_relTraceIdeal`), hence equals
`S`: `S` is a defect group. Conversely, a defect group `D` is conjugate to such an `S`
(`TauCeti.IsBlockIdempotent.isDefectGroup_conj`), so it centralizes a conjugate `y` of `x`, and it
lies in, hence equals, a Sylow `p`-subgroup of `C_G(y)`.

The statements hold over every field of characteristic `p`, given the homomorphism `λ_B`; over an
algebraically closed field it is `TauCeti.IsBlockIdempotent.centralCharacter`, and every block has
a defect class (`TauCeti.IsBlockIdempotent.exists_isDefectClass`).

## Main results

* `TauCeti.classSumCenter_mem_relTraceIdeal_centralizer`: the class sum of `x` is a trace from
  `C_G(x)`.
* `TauCeti.IsBlockIdempotent.mem_relTraceIdeal_of_apply_classSumCenter_ne_zero`: if
  `λ_B(K_C) ≠ 0` for the class `C` of `x`, then `e_B ∈ Tr_S^G(k[G]^S)` for every Sylow
  `p`-subgroup `S` of `C_G(x)`.
* `TauCeti.IsDefectClass.isDefectGroup_map_sylow`: for `x` in a defect class, every Sylow
  `p`-subgroup of `C_G(x)` is a defect group.
* `TauCeti.IsDefectClass.isDefectGroup_iff`: for a defect class `C`, the defect groups are exactly
  the Sylow `p`-subgroups of the centralizers `C_G(x)`, `x ∈ C`.

## References

* A. Martínez, *Modular representation theory of finite groups*, Definition 3.2, p. 17, and
  Theorem 4.3, p. 24.
-/

public section

namespace TauCeti

open MonoidAlgebra
open scoped Pointwise

variable {k G : Type*} [Group G] [Fintype G]

/-- **Class sums are traces from centralizers.** The class sum of `x`, an element of
`k[G]^G = Z(k[G])`, lies in `Tr_{C_G(x)}^G(k[G]^{C_G(x)})`: it is `Tr_{C_G(x)}^G(x)`. -/
theorem classSumCenter_mem_relTraceIdeal_centralizer [CommSemiring k] [DecidableEq G] (x : G) :
    (⟨classSumCenter (k := k) (ConjClasses.mk x),
        center_le_conjInvariants ⊤ (classSumCenter (ConjClasses.mk x)).property⟩ :
        conjInvariants k (⊤ : Subgroup G)) ∈
      relTraceIdeal k (le_top : Subgroup.centralizer {x} ≤ ⊤) := by
  rw [← relTraceIdeal_congr le_top (top_inf_eq (Subgroup.centralizer {x})) le_top,
    mem_relTraceIdeal_iff]
  refine ⟨⟨single x 1, single_mem_conjInvariants_inf_centralizer ⊤ x 1⟩, ?_⟩
  ext1
  ext h
  simp only [classSumCenter_coe]
  rw [coeff_relTrace_single_inf_centralizer, classSum_coeff]
  have hiff : (∃ q ∈ (⊤ : Subgroup G), q * x * q⁻¹ = h) ↔ ConjClasses.mk h = ConjClasses.mk x := by
    rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_comm, isConj_iff]
    simp
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hiff.1 h1) h2
  · exact absurd (hiff.2 h2) h1
  · rfl

variable [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]

/-- **A block is a trace from a Sylow subgroup of a centralizer.** Let `e_B` be a block idempotent
of `k[G]`, `k` a field of characteristic `p`, and `φ : Z(k[G]) → k` a `k`-algebra homomorphism
with `φ(e_B) = 1`. If `φ(K_C) ≠ 0` for the class `C` of `x`, then
`e_B ∈ Tr_S^G(k[G]^S)` for every Sylow `p`-subgroup `S` of `C_G(x)`: `K_C` is a trace from
`C_G(x)`, hence from `S`, and `e_B` is a multiple of `K_C`, since `Z(k[G]) e_B` is local and
`φ(K_C e_B) ≠ 0`. -/
theorem IsBlockIdempotent.mem_relTraceIdeal_of_apply_classSumCenter_ne_zero [DecidableEq G]
    {φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k}
    {b : Subalgebra.center k (MonoidAlgebra k G)} (hb : IsBlockIdempotent b) (hφ : φ b = 1)
    {x : G} (hx : φ (classSumCenter (ConjClasses.mk x)) ≠ 0)
    (S : Sylow p (Subgroup.centralizer {x})) :
    (⟨b, center_le_conjInvariants ⊤ b.property⟩ : conjInvariants k (⊤ : Subgroup G)) ∈
      relTraceIdeal k
        (le_top : (S : Subgroup (Subgroup.centralizer {x})).map (Subgroup.subtype _) ≤ ⊤) := by
  let C := Subgroup.centralizer {x}
  let P : Subgroup G := (S : Subgroup C).map C.subtype
  -- `Tr_P^G(k[G]^P) = Tr_{C_G(x)}^G(k[G]^{C_G(x)})`, which contains the class sum `K`.
  have hPC : P ≤ C := Subgroup.map_subtype_le _
  have hPS : P.subgroupOf C = S := by
    rw [← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  have hideal : relTraceIdeal k (le_top : P ≤ ⊤) = relTraceIdeal k (le_top : C ≤ ⊤) :=
    relTraceIdeal_eq_of_subgroupOf_eq_sylow hPC le_top S hPS
  -- `b = K z b` for some central `z`, by locality of `Z(k[G]) b`.
  set K := classSumCenter (k := k) (ConjClasses.mk x)
  obtain ⟨z, hz⟩ := hb.exists_mul_mul_eq_of_apply_ne_zero hφ hx
  let ι := Subalgebra.inclusion (center_le_conjInvariants (R := k) (G := G) ⊤)
  -- The statements write `ι c` in anonymous-constructor form; `hι` bridges the two.
  have hι (c : Subalgebra.center k (MonoidAlgebra k G)) :
      ι c = ⟨c, center_le_conjInvariants ⊤ c.property⟩ :=
    Subtype.ext (Subalgebra.coe_inclusion _ c)
  have hK : ι K ∈ relTraceIdeal k (le_top : P ≤ ⊤) := by
    rw [hι, hideal]
    exact classSumCenter_mem_relTraceIdeal_centralizer x
  have hb' : (⟨b, center_le_conjInvariants ⊤ b.property⟩ : conjInvariants k (⊤ : Subgroup G)) =
      ι K * ι (z * b) := by
    rw [← map_mul, ← mul_assoc, hz, hι]
  rw [hb']
  exact Ideal.mul_mem_right _ _ hK

/-- **Sylow subgroups of centralizers of a defect class are defect groups.** Let `e_B` be a block
idempotent of `k[G]`, `k` a field of characteristic `p`, and `φ : Z(k[G]) → k` a `k`-algebra
homomorphism with `φ(e_B) = 1`. If the class of `x` is a defect class of `e_B` for `φ`, then every
Sylow `p`-subgroup of `C_G(x)` is a defect group of `e_B` (Martínez, Theorem 4.3, p. 24). -/
theorem IsDefectClass.isDefectGroup_map_sylow [DecidableEq G]
    {φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k}
    {b : Subalgebra.center k (MonoidAlgebra k G)} (hb : IsBlockIdempotent b) (hφ : φ b = 1)
    {x : G} (hC : IsDefectClass φ b (ConjClasses.mk x)) (S : Sylow p (Subgroup.centralizer {x})) :
    IsDefectGroup k p (b : MonoidAlgebra k G)
      ((S : Subgroup (Subgroup.centralizer {x})).map (Subgroup.subtype _)) := by
  set P : Subgroup G := (S : Subgroup (Subgroup.centralizer {x})).map (Subgroup.subtype _)
  have hPp : IsPGroup p P := S.isPGroup.map _
  -- `x` centralizes `P`, and the coefficient of `Br_P(b)` at `x` is that of `b`.
  have hxP : x ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, -, rfl⟩
    exact (Subgroup.mem_centralizer_singleton_iff.1 y.property).eq
  have hBr : brauerProjection P (b : MonoidAlgebra k G) ≠ 0 := fun h => by
    have := congrArg (fun y => y.coeff (⟨x, hxP⟩ : Subgroup.centralizer (P : Set G))) h
    simp only [coeff_brauerProjection] at this
    exact hC.coeff_ne_zero this
  have hmem := hb.mem_relTraceIdeal_of_apply_classSumCenter_ne_zero hφ
    hC.apply_classSumCenter_ne_zero S
  exact TauCeti.isDefectGroup_iff.2 ⟨hPp, hBr, fun Q hQ hQb hPQ =>
    eq_of_le_of_mem_relTraceIdeal hmem hQ hQb hPQ⟩

/-- **Martínez's theorem.** Let `e_B` be a block idempotent of `k[G]`, `k` a field of
characteristic `p`, `φ : Z(k[G]) → k` a `k`-algebra homomorphism with `φ(e_B) = 1`, and `C` a
defect class of `e_B` for `φ`. The defect groups of `e_B` are exactly the Sylow `p`-subgroups of
the centralizers `C_G(x)`, `x ∈ C` (Martínez, Theorem 4.3, p. 24). -/
theorem IsDefectClass.isDefectGroup_iff [DecidableEq G]
    {φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k}
    {b : Subalgebra.center k (MonoidAlgebra k G)} (hb : IsBlockIdempotent b) (hφ : φ b = 1)
    {C : ConjClasses G} (hC : IsDefectClass φ b C) {D : Subgroup G} :
    IsDefectGroup k p (b : MonoidAlgebra k G) D ↔
      ∃ x, ConjClasses.mk x = C ∧ ∃ S : Sylow p (Subgroup.centralizer {x}),
        D = (S : Subgroup (Subgroup.centralizer {x})).map (Subgroup.subtype _) := by
  refine ⟨fun hD => ?_, ?_⟩
  · obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective C
    obtain ⟨S₀⟩ := Sylow.nonempty (p := p) (G := Subgroup.centralizer {g})
    obtain ⟨c, hc⟩ := hb.isDefectGroup_conj (p := p) (hC.isDefectGroup_map_sylow hb hφ S₀) hD
    -- The conjugate `D = c S₀ c⁻¹` centralizes `y = c g c⁻¹`.
    set y := c * g * c⁻¹
    have hy : ConjClasses.mk y = ConjClasses.mk g :=
      ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_iff.2 ⟨c, rfl⟩).symm
    have hDy : D ≤ Subgroup.centralizer {y} := by
      rw [hc]
      rintro _ ⟨_, ⟨s, -, rfl⟩, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hs := Subgroup.mem_centralizer_singleton_iff.1 s.property
      exact (Commute.conj_iff c).2 hs
    obtain ⟨S, hS⟩ := ((hD.isPGroup).comap_of_injective _
      (Subgroup.subtype_injective (Subgroup.centralizer {y}))).exists_le_sylow
    refine ⟨y, hy, S, ?_⟩
    have hDS : D ≤ (S : Subgroup (Subgroup.centralizer {y})).map (Subgroup.subtype _) := by
      intro d hd
      exact ⟨⟨d, hDy hd⟩, hS hd, rfl⟩
    have hCy : IsDefectClass φ b (ConjClasses.mk y) := hy ▸ hC
    exact ((TauCeti.isDefectGroup_iff.1 hD).2.2 _ (S.isPGroup.map _)
      (hCy.isDefectGroup_map_sylow hb hφ S).brauerProjection_ne_zero hDS).symm
  · rintro ⟨x, rfl, S, rfl⟩
    exact hC.isDefectGroup_map_sylow hb hφ S

end TauCeti
