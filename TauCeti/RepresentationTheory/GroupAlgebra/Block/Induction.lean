/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GroupAlgebra.Block.CentralCharacter
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Defect.Sylow
public import TauCeti.RepresentationTheory.GroupAlgebra.Brauer.Correspondent
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.NormalPSubgroup

/-!
# Block induction

Let `k` be a field of characteristic `p`, `G` a finite group and `f : H →* G` injective, for
instance the inclusion of a subgroup. For `z ∈ k[G]`, `z_H ∈ k[H]` keeps the coefficients on `H`
(`TauCeti.restrictCoeff`); it maps `Z(k[G])` to `Z(k[H])` (`TauCeti.centerRestrict`). A block
`B` of `k[G]` is **induced** from a block `b` of `k[H]`, `b^G = B`, when the central characters
satisfy `λ_B(z) = λ_b(z_H)` for every `z ∈ Z(k[G])` (`TauCeti.IsInducedBlock`; Sambale,
Definition 1.10, p. 16, and Martínez, p. 25, over an algebraically closed field). The map
`z ↦ λ_b(z_H)` is linear but need not be multiplicative, so `b^G` need not exist; it is unique
when it does.

The basic tool is that a central character only sees the centralizer of a defect group: if `D` is
a defect group of `b` and `w ∈ Z(k[H])` has no coefficient on `C_H(D)`, then `λ_b(w) = 0`
(`TauCeti.IsBlockIdempotent.apply_eq_zero_of_brauerProjection_eq_zero`). Indeed `λ_b(K_C) ≠ 0`
for a class sum `K_C` forces `D` into a Sylow `p`-subgroup of the centralizer of an element of
`C`, by the relative trace description of defect groups.

## Main results

* `TauCeti.existsUnique_isBlockIdempotent_apply_eq_one`: every `k`-algebra homomorphism
  `Z(k[G]) → k` is the central character of exactly one block.
* `TauCeti.IsBlockIdempotent.exists_isInducedBlock`: `b^G` is defined when `C_G(D) ≤ H` for a
  defect group `D` of `b` (Sambale, Proposition 1.11, p. 16): for central `z, w` the elements
  `(z w)_H` and `z_H w_H` agree on `C_H(D)` (`TauCeti.coeff_restrictCoeff_mul_of_mem_centralizer`).
* `TauCeti.IsInducedBlock.unique`, `TauCeti.IsInducedBlock.iff_centralCharacter`: uniqueness of
  `b^G`, and the defining relation for the central characters over an algebraically closed field.
* `TauCeti.IsInducedBlock.exists_isDefectGroup_le`: every defect group of `b` lies in a defect
  group of `b^G` (Sambale, Proposition 1.11, p. 16).
* `TauCeti.IsInducedBlock.trans`, `TauCeti.IsInducedBlock.of_comp`: block induction is
  transitive.
* `TauCeti.IsBlockIdempotent.centerBrauerProjection_eq_sum`: for a `p`-subgroup `P` with
  `P C_G(P) ≤ H ≤ N_G(P)` and `k` algebraically closed, `Br_P(e_B) = ∑_{b^G = B} e_b` (Martínez,
  Theorem 4.5 and Corollary 4.6, p. 26); `TauCeti.IsBlockIdempotent.brauerCorrespondent_eq_sum`
  is the case `H = N_G(P)`, for `TauCeti.brauerCorrespondent`.
* `TauCeti.IsInducedBlock.isDefectGroup_subgroupOf`: if `P` is a defect group of `B` and
  `P C_G(P) ≤ H ≤ N_G(P)`, every block `b` of `k[H]` with `b^G = B` has defect group `P`.

Brauer's first main theorem, that `B ↦ Br_D(e_B)` is a bijection from the blocks of `k[G]` with
defect group `D` onto those of `k[N_G(D)]` with defect group `D`, is not proved here: by the last
two results `Br_D(e_B)` is a sum of blocks of `k[N_G(D)]` with defect group `D` inducing `B`, and
what remains is that exactly one block occurs and that every such block induces a block with
defect group `D`.

## References

* B. Sambale, *Blocks of Finite Groups and Their Invariants*, Lecture Notes in Mathematics 2127,
  Definition 1.10 and Proposition 1.11, p. 16.
* A. Martínez, *Modular representation theory of finite groups*, p. 25, and Theorem 4.5 and
  Corollary 4.6, p. 26.
-/

public section

namespace TauCeti

open MonoidAlgebra
open scoped Pointwise

section Restrict

variable {k G H : Type*} [CommSemiring k] [Monoid G] [Monoid H]

/-- The **restriction of coefficients** `k[G] → k[H]` along an injective homomorphism
`f : H →* G`: the coefficient of `restrictCoeff f hf x` at `h` is that of `x` at `f h`. For a
subgroup `H ≤ G` it sends `z` to `z_H`, which keeps the coefficients on `H`. -/
noncomputable def restrictCoeff (f : H →* G) (hf : Function.Injective f) :
    MonoidAlgebra k G →ₗ[k] MonoidAlgebra k H where
  toFun := comapDomain f hf
  map_add' := comapDomain_add _ _
  map_smul' c x := by
    ext
    simp

/-- The coefficient of `restrictCoeff f hf x` at `h` is the coefficient of `x` at `f h`. -/
@[simp]
theorem coeff_restrictCoeff (f : H →* G) (hf : Function.Injective f) (x : MonoidAlgebra k G)
    (h : H) : (restrictCoeff f hf x).coeff h = x.coeff (f h) := by
  simp [restrictCoeff]

/-- Restriction of coefficients along a composite is the composite of the restrictions. -/
theorem restrictCoeff_comp {K : Type*} [Monoid K] (f₂ : H →* G) (hf₂ : Function.Injective f₂)
    (f₁ : K →* H) (hf₁ : Function.Injective f₁) (x : MonoidAlgebra k G) :
    restrictCoeff (f₂.comp f₁) (hf₂.comp hf₁) x =
      restrictCoeff f₁ hf₁ (restrictCoeff f₂ hf₂ x) := by
  ext
  simp

/-- The restriction of `1` is `1`. -/
@[simp]
theorem restrictCoeff_one (f : H →* G) (hf : Function.Injective f) :
    restrictCoeff f hf (1 : MonoidAlgebra k G) = 1 := by
  change comapDomain f hf _ = _
  rw [one_def, one_def, ← map_one f, comapDomain_single_map]

end Restrict

section CenterRestrict

variable {k G H : Type*} [CommSemiring k] [Group G] [Group H]

/-- The restriction of a central element is central: its coefficients are constant on conjugacy
classes of `G`, hence on those of `H`. -/
theorem restrictCoeff_mem_center (f : H →* G) (hf : Function.Injective f)
    {z : MonoidAlgebra k G} (hz : z ∈ Subalgebra.center k (MonoidAlgebra k G)) :
    restrictCoeff f hf z ∈ Subalgebra.center k (MonoidAlgebra k H) := by
  rw [← conjInvariants_top, mem_conjInvariants_iff_coeff] at hz ⊢
  intro h _ g
  simpa using hz (f h) trivial (f g)

/-- The restriction of coefficients `Z(k[G]) → Z(k[H])` on centres, `z ↦ z_H`. -/
noncomputable def centerRestrict (f : H →* G) (hf : Function.Injective f) :
    Subalgebra.center k (MonoidAlgebra k G) →ₗ[k] Subalgebra.center k (MonoidAlgebra k H) where
  toFun z := ⟨restrictCoeff f hf z, restrictCoeff_mem_center f hf z.property⟩
  map_add' z w := Subtype.ext (map_add (restrictCoeff f hf) (z : MonoidAlgebra k G) w)
  map_smul' c z := Subtype.ext (map_smul (restrictCoeff f hf) c (z : MonoidAlgebra k G))

/-- `centerRestrict f hf z` is `restrictCoeff f hf z`. -/
@[simp]
theorem coe_centerRestrict (f : H →* G) (hf : Function.Injective f)
    (z : Subalgebra.center k (MonoidAlgebra k G)) :
    (centerRestrict f hf z : MonoidAlgebra k H) = restrictCoeff f hf z :=
  (rfl)

/-- The restriction of `1` on centres is `1`. -/
@[simp]
theorem centerRestrict_one (f : H →* G) (hf : Function.Injective f) :
    centerRestrict f hf (1 : Subalgebra.center k (MonoidAlgebra k G)) = 1 :=
  Subtype.ext (by simp)

/-- Restriction on centres along a composite is the composite of the restrictions. -/
theorem centerRestrict_comp {K : Type*} [Group K] (f₂ : H →* G) (hf₂ : Function.Injective f₂)
    (f₁ : K →* H) (hf₁ : Function.Injective f₁) (z : Subalgebra.center k (MonoidAlgebra k G)) :
    centerRestrict (f₂.comp f₁) (hf₂.comp hf₁) z =
      centerRestrict f₁ hf₁ (centerRestrict f₂ hf₂ z) :=
  Subtype.ext (by simpa using restrictCoeff_comp f₂ hf₂ f₁ hf₁ (z : MonoidAlgebra k G))

end CenterRestrict

section Character

variable {k G : Type*} [Field k] [Monoid G] [Finite G]

/-- **Every character of the centre belongs to exactly one block.** For a `k`-algebra
homomorphism `ψ : Z(k[G]) → k`, `G` finite, there is exactly one block idempotent `e_B` with
`ψ(e_B) = 1`: the values of `ψ` at a complete family of block idempotents are `0` or `1` and sum
to `1`, and two blocks with value `1` have product of value `1`, so are equal. -/
theorem existsUnique_isBlockIdempotent_apply_eq_one
    (ψ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k) :
    ∃! b : Subalgebra.center k (MonoidAlgebra k G), IsBlockIdempotent b ∧ ψ b = 1 := by
  obtain ⟨n, e, he, hep⟩ := exists_completeOrthogonalIdempotents_isBlockIdempotent k G
  obtain ⟨i, hi⟩ : ∃ i, ψ (e i) ≠ 0 := by
    by_contra! h
    have := congrArg ψ he.complete
    simp [map_sum, h] at this
  have h1 : ψ (e i) = 1 := ((he.idem i).map ψ).eq_zero_or_one.resolve_left hi
  refine ⟨e i, ⟨hep i, h1⟩, fun b hb ↦ hb.1.eq_of_commute_of_mul_ne_zero (hep i)
    (Commute.all _ _) fun h0 ↦ ?_⟩
  have := congrArg ψ h0
  rw [map_mul, hb.2, h1, mul_one, map_zero] at this
  exact one_ne_zero this

omit [Finite G] in
/-- Two distinct block idempotents are orthogonal. -/
theorem IsBlockIdempotent.mul_eq_zero_of_ne {b b' : Subalgebra.center k (MonoidAlgebra k G)}
    (hb : IsBlockIdempotent b) (hb' : IsBlockIdempotent b') (h : b ≠ b') : b * b' = 0 := by
  by_contra h0
  exact h (hb.eq_of_commute_of_mul_ne_zero hb' (Commute.all _ _) h0)

omit [Finite G] in
/-- A `k`-algebra homomorphism `Z(k[G]) → k` with value `1` at a block idempotent `e_B` vanishes
at every other block idempotent. -/
theorem IsBlockIdempotent.apply_eq_zero_of_ne {φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k}
    {b b' : Subalgebra.center k (MonoidAlgebra k G)} (hb : IsBlockIdempotent b)
    (hb' : IsBlockIdempotent b') (hφ : φ b = 1) (h : b ≠ b') : φ b' = 0 := by
  have := congrArg φ (hb.mul_eq_zero_of_ne hb' h)
  rwa [map_mul, hφ, one_mul, map_zero] at this

end Character

section DefectCentralizer

variable {k G : Type*} [Field k] [Group G] [Finite G] {p : ℕ} [Fact p.Prime] [CharP k p]

/-- **Central characters only see the centralizer of a defect group.** Let `e_B` be a block
idempotent of `k[G]`, `k` a field of characteristic `p`, `φ : Z(k[G]) → k` a `k`-algebra
homomorphism with `φ(e_B) = 1` and `D` a defect group of `e_B`. If `w ∈ Z(k[G])` has
`Br_D(w) = 0`, that is no coefficient on `C_G(D)`, then `φ(w) = 0`.

Write `w = ∑_C a_w(C) K_C` in the class sums. If `φ(K_C) ≠ 0` for the class `C` of `x`, then
`e_B ∈ Tr_S^G(k[G]^S)` for a Sylow `p`-subgroup `S` of `C_G(x)`
(`TauCeti.IsBlockIdempotent.mem_relTraceIdeal_of_apply_classSumCenter_ne_zero`), so `D` lies in a
conjugate of `S` (`TauCeti.exists_le_conj_of_mem_relTraceIdeal`), and so centralizes a conjugate
`y` of `x`; then `a_w(C) = w_y = 0`. -/
theorem IsBlockIdempotent.apply_eq_zero_of_brauerProjection_eq_zero
    {φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k}
    {b : Subalgebra.center k (MonoidAlgebra k G)} (hb : IsBlockIdempotent b) (hφ : φ b = 1)
    {D : Subgroup G} (hD : IsDefectGroup k p (b : MonoidAlgebra k G) D)
    {w : Subalgebra.center k (MonoidAlgebra k G)}
    (hw : brauerProjection D (w : MonoidAlgebra k G) = 0) : φ w = 0 := by
  classical
  have := Fintype.ofFinite G
  rw [brauerProjection_eq_zero_iff] at hw
  rw [← classSumBasis.sum_repr w, map_sum]
  refine Finset.sum_eq_zero fun C _ ↦ ?_
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective C
  rw [map_smul, classSumBasis_apply, smul_eq_mul]
  by_cases hx : φ (classSumCenter (ConjClasses.mk x)) = 0
  · rw [hx, mul_zero]
  obtain ⟨S⟩ := Sylow.nonempty (p := p) (G := Subgroup.centralizer {x})
  have hmem := hb.mem_relTraceIdeal_of_apply_classSumCenter_ne_zero hφ hx S
  obtain ⟨g, hg⟩ := exists_le_conj_of_mem_relTraceIdeal hmem hD.isPGroup
    hD.brauerProjection_ne_zero
  -- `D` centralizes `y = g x g⁻¹`.
  have hy : g * x * g⁻¹ ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    obtain ⟨s, -, hs⟩ := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.1 (hg hd)
    have hds : d = g * s * g⁻¹ := by
      simp only [Subgroup.coe_subtype] at hs
      rw [hs]
      simp [MulAut.smul_def, mul_assoc]
    have hcomm : (s : G) * x = x * s := (Subgroup.mem_centralizer_singleton_iff.1 s.property).eq
    rw [hds]
    calc g * s * g⁻¹ * (g * x * g⁻¹) = g * (s * x) * g⁻¹ := by group
      _ = g * (x * s) * g⁻¹ := by rw [hcomm]
      _ = g * x * g⁻¹ * (g * s * g⁻¹) := by group
  have h0 := hw _ hy
  rw [center_coeff_eq_of_isConj w (isConj_iff.2 ⟨g, rfl⟩).symm] at h0
  rw [classSumBasis_repr_apply, centerToConjClasses_mk, h0, zero_mul]

end DefectCentralizer

section Multiplicative

variable {k G H : Type*} [CommSemiring k] [Group G] [Group H] [Finite G] {p : ℕ} [Fact p.Prime]
  [CharP k p]

/-- **Restriction is multiplicative on the centralizer of a `p`-subgroup.** Let `f : H →* G` be
injective, `G` finite, `D` a `p`-subgroup of `H` with `C_G(f(D)) ≤ f(H)`, and `k` of
characteristic `p`. For central `z, w ∈ k[G]` and `x ∈ C_H(D)`, the coefficients of `(z w)_H` and
`z_H w_H` at `x` agree.

The coefficient of `(z w)_H` at `x` is `∑_{a ∈ G} z_a w_{a⁻¹ f(x)}`, that of `z_H w_H` the same sum
over `a ∈ f(H)`. Both summands are invariant under conjugation by the `p`-group `f(D)`, which
fixes `f(x)`, so both sums are their sums over `C_G(f(D))`
(`IsPGroup.sum_eq_sum_centralizer_of_nsmul_eq_zero`), and `C_G(f(D)) ≤ f(H)`. -/
theorem coeff_restrictCoeff_mul_of_mem_centralizer (f : H →* G) (hf : Function.Injective f)
    {D : Subgroup H} (hD : IsPGroup p D)
    (hC : Subgroup.centralizer ((D.map f : Subgroup G) : Set G) ≤ f.range)
    {z w : MonoidAlgebra k G} (hz : z ∈ Subalgebra.center k (MonoidAlgebra k G))
    (hw : w ∈ Subalgebra.center k (MonoidAlgebra k G)) {x : H}
    (hx : x ∈ Subgroup.centralizer (D : Set H)) :
    (restrictCoeff f hf (z * w)).coeff x =
      (restrictCoeff f hf z * restrictCoeff f hf w).coeff x := by
  classical
  have := Fintype.ofFinite G
  have : Finite H := Finite.of_injective f hf
  have := Fintype.ofFinite H
  rw [← conjInvariants_top, mem_conjInvariants_iff_coeff] at hz hw
  have hp : ∀ r : k, p • r = 0 := fun r => by rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  -- `f x` centralizes `f(D)`.
  have hfx : ∀ g ∈ D.map f, g * f x = f x * g := by
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hx d hd]
  set F : G → k := fun a => z.coeff a * w.coeff (a⁻¹ * f x) with hF
  set F' : G → k := fun a => if a ∈ f.range then F a else 0 with hF'
  have hFinv : ∀ g ∈ D.map f, ∀ a : G, F (g * a * g⁻¹) = F a := by
    intro g hg a
    have hc : g⁻¹ * f x = f x * g⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hfx g hg, mul_inv_cancel_right]
    have : (g * a * g⁻¹)⁻¹ * f x = g * (a⁻¹ * f x) * g⁻¹ :=
      calc (g * a * g⁻¹)⁻¹ * f x = g * a⁻¹ * (g⁻¹ * f x) := by group
        _ = g * a⁻¹ * (f x * g⁻¹) := by rw [hc]
        _ = g * (a⁻¹ * f x) * g⁻¹ := by group
    simp only [hF, this, hz g trivial, hw g trivial]
  have hF'inv : ∀ g ∈ D.map f, ∀ a : G, F' (g * a * g⁻¹) = F' a := by
    intro g hg a
    have hgr : g ∈ f.range := Subgroup.map_le_range f D hg
    have hiff : g * a * g⁻¹ ∈ f.range ↔ a ∈ f.range := by
      refine ⟨fun h => ?_, fun h => mul_mem (mul_mem hgr h) (inv_mem hgr)⟩
      have := mul_mem (mul_mem (inv_mem hgr) h) hgr
      simpa [mul_assoc] using this
    simp only [hF', hiff, hFinv g hg a]
  have h1 : ∑ a : H, z.coeff (f a) * w.coeff (f (a⁻¹ * x)) = ∑ a, F' a := by
    refine Fintype.sum_of_injective f hf _ F' (fun a ha => ?_) fun a => ?_
    · simp only [hF', MonoidHom.mem_range]
      rw [ite_eq_right_iff.2 fun h => absurd (by simpa using h) ha]
    · simp [hF', hF, map_mul, map_inv]
  have h2 := IsPGroup.sum_eq_sum_centralizer_of_nsmul_eq_zero (hD.map f) hp F hFinv
  have h3 := IsPGroup.sum_eq_sum_centralizer_of_nsmul_eq_zero (hD.map f) hp F' hF'inv
  rw [coeff_restrictCoeff, coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp),
    coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp)]
  simp only [coeff_restrictCoeff]
  rw [h1, h3]
  refine Eq.trans h2 (Finset.sum_congr rfl fun a ha => ?_)
  simp only [hF']
  rw [ite_eq_left (hC (Finset.mem_filter.1 ha).2)]

end Multiplicative

section Induction

variable {k G H : Type*} [Field k] [Group G] [Group H] [Finite G]

variable (k) in
/-- **Block induction.** For an injective homomorphism `f : H →* G`, for instance the inclusion
of a subgroup, a block `B` of `k[G]` is **induced** from a block `b` of `k[H]`, written
`b^G = B`, when the central characters satisfy `λ_B(z) = λ_b(z_H)` for every `z ∈ Z(k[G])`, where
`z_H` keeps the coefficients on `H` (`TauCeti.centerRestrict`). Central characters are unique when
they exist (`TauCeti.IsPrimitiveIdempotent.algHom_ext`), and over an algebraically closed field
they exist (`TauCeti.IsBlockIdempotent.centralCharacter`); `B` is then unique when it exists
(`TauCeti.IsInducedBlock.unique`). -/
def IsInducedBlock (f : H →* G) (hf : Function.Injective f)
    (b : Subalgebra.center k (MonoidAlgebra k H)) (B : Subalgebra.center k (MonoidAlgebra k G)) :
    Prop :=
  IsBlockIdempotent b ∧ IsBlockIdempotent B ∧
    ∃ (φ : Subalgebra.center k (MonoidAlgebra k H) →ₐ[k] k)
      (ψ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k),
      φ b = 1 ∧ ψ B = 1 ∧ ∀ z, ψ z = φ (centerRestrict f hf z)

namespace IsInducedBlock

variable {f : H →* G} {hf : Function.Injective f} {b : Subalgebra.center k (MonoidAlgebra k H)}
  {B : Subalgebra.center k (MonoidAlgebra k G)}

omit [Finite G] in
/-- An induced block is a block of `k[H]`. -/
theorem isBlockIdempotent_left (h : IsInducedBlock k f hf b B) : IsBlockIdempotent b :=
  h.1

omit [Finite G] in
/-- The induced block is a block of `k[G]`. -/
theorem isBlockIdempotent_right (h : IsInducedBlock k f hf b B) : IsBlockIdempotent B :=
  h.2.1

/-- **The defining relation, for any choice of characters.** If `b^G = B`, then for all
`k`-algebra homomorphisms `φ : Z(k[H]) → k` and `ψ : Z(k[G]) → k` with `φ(e_b) = 1` and
`ψ(e_B) = 1`, `ψ(z) = φ(z_H)`. -/
theorem apply_eq (h : IsInducedBlock k f hf b B)
    {φ : Subalgebra.center k (MonoidAlgebra k H) →ₐ[k] k}
    {ψ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k} (hφ : φ b = 1) (hψ : ψ B = 1)
    (z : Subalgebra.center k (MonoidAlgebra k G)) : ψ z = φ (centerRestrict f hf z) := by
  have : Finite H := Finite.of_injective f hf
  obtain ⟨hb, hB, φ', ψ', hφ', hψ', hrel⟩ := h
  rw [hB.algHom_ext hψ hψ', hb.algHom_ext hφ hφ', hrel]

/-- **Uniqueness of the induced block.** `b^G`, when defined, is unique. -/
theorem unique {B' : Subalgebra.center k (MonoidAlgebra k G)} (h : IsInducedBlock k f hf b B)
    (h' : IsInducedBlock k f hf b B') : B = B' := by
  have : Finite H := Finite.of_injective f hf
  obtain ⟨hb, hB, φ, ψ, hφ, hψ, hrel⟩ := h
  obtain ⟨-, hB', φ', ψ', hφ', hψ', hrel'⟩ := h'
  have hψB' : ψ B' = 1 := by
    rw [hrel, hb.algHom_ext hφ hφ', ← hrel', hψ']
  exact (existsUnique_isBlockIdempotent_apply_eq_one ψ).unique ⟨hB, hψ⟩ ⟨hB', hψB'⟩

/-- **Transitivity of block induction.** For injective `f₁ : K →* H` and `f₂ : H →* G`, if
`b^H = c` and `c^G = B`, then `b^G = B` along `f₂ ∘ f₁`. -/
theorem trans {K : Type*} [Group K] {f₁ : K →* H} {hf₁ : Function.Injective f₁}
    {b : Subalgebra.center k (MonoidAlgebra k K)} {c : Subalgebra.center k (MonoidAlgebra k H)}
    (h₁ : IsInducedBlock k f₁ hf₁ b c) (h₂ : IsInducedBlock k f hf c B) :
    IsInducedBlock k (f.comp f₁) (hf.comp hf₁) b B := by
  have : Finite H := Finite.of_injective f hf
  obtain ⟨hb, hc, φ, χ, hφ, hχ, hrel₁⟩ := h₁
  obtain ⟨-, hB, χ', ψ, hχ', hψ, hrel₂⟩ := h₂
  refine ⟨hb, hB, φ, ψ, hφ, hψ, fun z => ?_⟩
  rw [hrel₂, hc.algHom_ext hχ' hχ, hrel₁, centerRestrict_comp]

/-- **Block induction in stages.** For injective `f₁ : K →* H` and `f₂ : H →* G`, if `b^H = c`
and `b^G = B` along `f₂ ∘ f₁`, then `c^G = B`. -/
theorem of_comp {K : Type*} [Group K] {f₁ : K →* H} {hf₁ : Function.Injective f₁}
    {b : Subalgebra.center k (MonoidAlgebra k K)} {c : Subalgebra.center k (MonoidAlgebra k H)}
    (h₁ : IsInducedBlock k f₁ hf₁ b c) (h : IsInducedBlock k (f.comp f₁) (hf.comp hf₁) b B) :
    IsInducedBlock k f hf c B := by
  have : Finite K := Finite.of_injective _ (hf.comp hf₁)
  obtain ⟨hb, hc, φ, χ, hφ, hχ, hrel₁⟩ := h₁
  obtain ⟨-, hB, φ', ψ, hφ', hψ, hrel⟩ := h
  refine ⟨hc, hB, χ, ψ, hχ, hψ, fun z => ?_⟩
  rw [hrel, hrel₁, centerRestrict_comp, hb.algHom_ext hφ' hφ]

/-- **The defining relation for central characters.** Over an algebraically closed field,
`b^G = B` exactly when `λ_B(z) = λ_b(z_H)` for every `z ∈ Z(k[G])`. -/
theorem iff_centralCharacter [Finite H] [IsAlgClosed k] (hb : IsBlockIdempotent b)
    (hB : IsBlockIdempotent B) :
    IsInducedBlock k f hf b B ↔
      ∀ z, hB.centralCharacter z = hb.centralCharacter (centerRestrict f hf z) :=
  ⟨fun h => h.apply_eq hb.centralCharacter_self hB.centralCharacter_self,
    fun h => ⟨hb, hB, _, _, hb.centralCharacter_self, hB.centralCharacter_self, h⟩⟩

variable {p : ℕ} [Fact p.Prime] [CharP k p]

/-- **Defect groups grow under block induction** (Sambale, Proposition 1.11, p. 16). If
`b^G = B` along `f : H →* G` and `D` is a defect group of `b`, then `f(D)` lies in a defect group
of `B`.

Let `C` be a defect class of `B` (`TauCeti.exists_isDefectClass`), so `λ_B(K_C) ≠ 0`. Then
`λ_b((K_C)_H) ≠ 0`, so `(K_C)_H` has a nonzero coefficient at some `c ∈ C_H(D)`
(`TauCeti.IsBlockIdempotent.apply_eq_zero_of_brauerProjection_eq_zero`): `f(c) ∈ C` and `f(D)`
centralizes `f(c)`. So `f(D)` lies in a Sylow `p`-subgroup of `C_G(f(c))`, which is a defect group
of `B` (`TauCeti.IsDefectClass.isDefectGroup_map_sylow`). -/
theorem exists_isDefectGroup_le (h : IsInducedBlock k f hf b B) {D : Subgroup H}
    (hD : IsDefectGroup k p (b : MonoidAlgebra k H) D) :
    ∃ E, IsDefectGroup k p (B : MonoidAlgebra k G) E ∧ D.map f ≤ E := by
  classical
  have := Fintype.ofFinite G
  have : Finite H := Finite.of_injective f hf
  obtain ⟨hb, hB, φ, ψ, hφ, hψ, hrel⟩ := h
  obtain ⟨C, hC⟩ := exists_isDefectClass hψ
  have hψC := hC.apply_classSumCenter_ne_zero
  rw [hrel] at hψC
  have hBr := mt (hb.apply_eq_zero_of_brauerProjection_eq_zero hφ hD) hψC
  rw [brauerProjection_eq_zero_iff, not_forall] at hBr
  obtain ⟨c, hc⟩ := hBr
  rw [Classical.not_imp] at hc
  obtain ⟨hc, hcC⟩ := hc
  rw [coe_centerRestrict, coeff_restrictCoeff, classSumCenter_coe, classSum_coeff] at hcC
  have hyC : ConjClasses.mk (f c) = C := by
    by_contra hne
    simp [hne] at hcC
  subst hyC
  -- `f(D)` centralizes `f c`.
  have hDy : D.map f ≤ Subgroup.centralizer {f c} := by
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Commute.map (Subgroup.mem_centralizer_iff.1 hc d hd) f
  obtain ⟨S, hS⟩ := ((hD.isPGroup.map f).comap_of_injective _
    (Subgroup.subtype_injective (Subgroup.centralizer {f c}))).exists_le_sylow
  refine ⟨_, hC.isDefectGroup_map_sylow hB hψ S, fun d hd => ⟨⟨d, hDy hd⟩, hS hd, rfl⟩⟩

omit [Finite G] in
/-- **Induction along the identity.** A block with a central character induces itself along the
identity of `G`. -/
theorem _root_.TauCeti.IsBlockIdempotent.isInducedBlock_id
    {b : Subalgebra.center k (MonoidAlgebra k H)} (hb : IsBlockIdempotent b)
    {φ : Subalgebra.center k (MonoidAlgebra k H) →ₐ[k] k} (hφ : φ b = 1) :
    IsInducedBlock k (MonoidHom.id H) Function.injective_id b b :=
  ⟨hb, hb, φ, φ, hφ, hφ, fun z => congrArg φ (Subtype.ext (by ext; simp))⟩

end IsInducedBlock

end Induction

section Existence

variable {k G H : Type*} [Field k] [Group G] [Group H] [Finite G] {p : ℕ}
  [Fact p.Prime] [CharP k p] {f : H →* G} {hf : Function.Injective f}
  {φ : Subalgebra.center k (MonoidAlgebra k H) →ₐ[k] k}
  {b : Subalgebra.center k (MonoidAlgebra k H)} {D : Subgroup H}

/-- **Restriction is multiplicative under a central character.** Let `e_b` be a block idempotent
of `k[H]` with a `k`-algebra homomorphism `φ : Z(k[H]) → k`, `φ(e_b) = 1`, and a defect group `D`
with `C_G(f(D)) ≤ f(H)`. Then `z ↦ φ(z_H)` is multiplicative on `Z(k[G])`: `(z w)_H - z_H w_H`
has no coefficient on `C_H(D)` (`TauCeti.coeff_restrictCoeff_mul_of_mem_centralizer`), so `φ`
kills it (`TauCeti.IsBlockIdempotent.apply_eq_zero_of_brauerProjection_eq_zero`). -/
theorem IsBlockIdempotent.apply_centerRestrict_mul (hb : IsBlockIdempotent b) (hφ : φ b = 1)
    (hD : IsDefectGroup k p (b : MonoidAlgebra k H) D)
    (hC : Subgroup.centralizer ((D.map f : Subgroup G) : Set G) ≤ f.range)
    (z w : Subalgebra.center k (MonoidAlgebra k G)) :
    φ (centerRestrict f hf (z * w)) = φ (centerRestrict f hf z) * φ (centerRestrict f hf w) := by
  have : Finite H := Finite.of_injective f hf
  rw [← map_mul, ← sub_eq_zero, ← map_sub]
  refine hb.apply_eq_zero_of_brauerProjection_eq_zero hφ hD ?_
  rw [brauerProjection_eq_zero_iff]
  intro c hc
  simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, coe_centerRestrict, coeff_sub,
    Finsupp.coe_sub, Pi.sub_apply]
  rw [sub_eq_zero]
  exact coeff_restrictCoeff_mul_of_mem_centralizer f hf hD.isPGroup hC z.property w.property hc

/-- **Existence of the induced block** (Sambale, Proposition 1.11, p. 16). Let `e_b` be a block
idempotent of `k[H]`, `k` a field of characteristic `p`, with a `k`-algebra homomorphism
`φ : Z(k[H]) → k`, `φ(e_b) = 1`, and a defect group `D` whose centralizer satisfies
`C_G(f(D)) ≤ f(H)`. Then `b^G` is defined: `z ↦ φ(z_H)` is a `k`-algebra homomorphism
(`TauCeti.IsBlockIdempotent.apply_centerRestrict_mul`), and so the central character of exactly
one block of `k[G]` (`TauCeti.existsUnique_isBlockIdempotent_apply_eq_one`). -/
theorem IsBlockIdempotent.exists_isInducedBlock (hb : IsBlockIdempotent b) (hφ : φ b = 1)
    (hD : IsDefectGroup k p (b : MonoidAlgebra k H) D)
    (hC : Subgroup.centralizer ((D.map f : Subgroup G) : Set G) ≤ f.range) :
    ∃ B, IsInducedBlock k f hf b B := by
  let ψ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k :=
    AlgHom.ofLinearMap (φ.toLinearMap ∘ₗ centerRestrict f hf) (by simp)
      (hb.apply_centerRestrict_mul hφ hD hC)
  obtain ⟨B, ⟨hB, hψ⟩, -⟩ := existsUnique_isBlockIdempotent_apply_eq_one ψ
  exact ⟨B, hb, hB, φ, ψ, hφ, hψ, fun _ => rfl⟩

end Existence

section BrauerFormula

variable {k G : Type*} [Field k] [Group G] {P H : Subgroup G}

/-- The coefficient of `Br_P(x)`, read in `k[H]` through `C_G(P) ≤ H`, at `h ∈ H` is the
coefficient of `x` at `h` when `h` centralizes `P`, and `0` otherwise. -/
theorem coeff_mapDomainRingHom_inclusion_brauerProjection
    (hCH : Subgroup.centralizer (P : Set G) ≤ H) (x : MonoidAlgebra k G) (h : H)
    [Decidable ((h : G) ∈ Subgroup.centralizer (P : Set G))] :
    (mapDomainRingHom k (Subgroup.inclusion hCH) (brauerProjection P x)).coeff h =
      if (h : G) ∈ Subgroup.centralizer (P : Set G) then x.coeff h else 0 := by
  rw [mapDomainRingHom_apply, coeff_mapDomain]
  split_ifs with hh
  · have hincl : Subgroup.inclusion hCH ⟨h, hh⟩ = h := Subtype.ext (Subgroup.coe_inclusion _ _)
    rw [← hincl, Finsupp.mapDomain_apply_of_injective (Subgroup.inclusion_injective _),
      coeff_brauerProjection, Subgroup.coe_inclusion]
  · refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨c, rfl⟩
    exact hh c.property

/-- **`Br_P` of a central element is central in `k[H]` for `H ≤ N_G(P)`.** For
`C_G(P) ≤ H ≤ N_G(P)` and `z ∈ Z(k[G])`, `Br_P(z)`, read in `k[H]`, is central: its coefficients
are those of `z` on `C_G(P)`, which is normalized by `H`. -/
theorem mapDomainRingHom_inclusion_brauerProjection_mem_center
    (hCH : Subgroup.centralizer (P : Set G) ≤ H) (hHN : H ≤ Subgroup.normalizer (P : Set G))
    {z : MonoidAlgebra k G} (hz : z ∈ Subalgebra.center k (MonoidAlgebra k G)) :
    mapDomainRingHom k (Subgroup.inclusion hCH) (brauerProjection P z) ∈
      Subalgebra.center k (MonoidAlgebra k H) := by
  classical
  rw [← conjInvariants_top, mem_conjInvariants_iff_coeff]
  rw [← conjInvariants_top, mem_conjInvariants_iff_coeff] at hz
  intro h _ n
  have hnormal : ∀ g ∈ H, ∀ c ∈ Subgroup.centralizer (P : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (P : Set G) := fun g hg c hc =>
    (Subgroup.normal_subgroupOf_iff (Subgroup.centralizer_le_normalizer (P : Set G))).1
      inferInstance c g hc (hHN hg)
  rw [coeff_mapDomainRingHom_inclusion_brauerProjection,
    coeff_mapDomainRingHom_inclusion_brauerProjection]
  have hiff : ((h * n * h⁻¹ : H) : G) ∈ Subgroup.centralizer (P : Set G) ↔
      (n : G) ∈ Subgroup.centralizer (P : Set G) := by
    refine ⟨fun hc => ?_, fun hc => by simpa using hnormal h h.property _ hc⟩
    simpa [mul_assoc] using hnormal _ (inv_mem h.property) _ hc
  simp only [hiff]
  split_ifs
  · simpa using hz h trivial n
  · rfl

/-- `Br_P(z)` of a central `z ∈ k[G]`, read in `Z(k[H])` for `C_G(P) ≤ H ≤ N_G(P)`: the element of
`Z(k[H])` with the coefficients of `z` on `C_G(P)` and `0` elsewhere. For `H = N_G(P)` it is
`TauCeti.brauerCorrespondent P z`. -/
noncomputable def centerBrauerProjection (hCH : Subgroup.centralizer (P : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G)) (z : Subalgebra.center k (MonoidAlgebra k G)) :
    Subalgebra.center k (MonoidAlgebra k H) :=
  ⟨mapDomainRingHom k (Subgroup.inclusion hCH) (brauerProjection P (z : MonoidAlgebra k G)),
    mapDomainRingHom_inclusion_brauerProjection_mem_center hCH hHN z.property⟩

/-- `centerBrauerProjection hCH hHN z` is `Br_P(z)` read in `k[H]`. -/
@[simp]
theorem coe_centerBrauerProjection (hCH : Subgroup.centralizer (P : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G)) (z : Subalgebra.center k (MonoidAlgebra k G)) :
    (centerBrauerProjection hCH hHN z : MonoidAlgebra k H) =
      mapDomainRingHom k (Subgroup.inclusion hCH) (brauerProjection P (z : MonoidAlgebra k G)) :=
  (rfl)

variable [Finite G] {p : ℕ} [Fact p.Prime] [CharP k p]

/-- For a `p`-subgroup `P` in characteristic `p`, `Br_P(e)` of a central idempotent `e`, read in
`Z(k[H])`, is idempotent: `Br_P` is multiplicative on `k[G]^P` (`TauCeti.brauerProjection_mul`). -/
theorem isIdempotentElem_centerBrauerProjection (hP : IsPGroup p P)
    (hCH : Subgroup.centralizer (P : Set G) ≤ H) (hHN : H ≤ Subgroup.normalizer (P : Set G))
    {e : Subalgebra.center k (MonoidAlgebra k G)} (he : IsIdempotentElem e) :
    IsIdempotentElem (centerBrauerProjection hCH hHN e) := by
  have he' : IsIdempotentElem (e : MonoidAlgebra k G) :=
    he.map (Subalgebra.center k (MonoidAlgebra k G)).val
  refine Subtype.ext ?_
  simp only [Subalgebra.coe_mul, coe_centerBrauerProjection]
  rw [← map_mul, ← brauerProjection_mul hP (center_le_conjInvariants P e.property)
    (center_le_conjInvariants P e.property), he'.eq]

/-- Every block `b` of `k[H]`, for `P C_G(P) ≤ H ≤ N_G(P)` with `P` a `p`-subgroup and `k`
algebraically closed of characteristic `p`, induces a block `B'` of `k[G]`, and
`λ_b(Br_P(e_B)) = λ_{B'}(e_B)` for every block `B` of `k[G]`.

The defect groups `D` of `b` contain the normal `p`-subgroup `P` of `H`
(`TauCeti.IsBlockIdempotent.le_of_isDefectGroup_of_isPGroup_of_normal`), so
`C_G(D) ≤ C_G(P) ≤ H` and `b^G` is defined (`TauCeti.IsBlockIdempotent.exists_isInducedBlock`).
`Br_P(e_B)` and `(e_B)_H` agree on `C_H(D) ≤ C_G(P)`, so `λ_b` takes the same value on them
(`TauCeti.IsBlockIdempotent.apply_eq_zero_of_brauerProjection_eq_zero`), and
`λ_b((e_B)_H) = λ_{B'}(e_B)`. -/
theorem IsBlockIdempotent.exists_isInducedBlock_centralCharacter_centerBrauerProjection
    [IsAlgClosed k] (hP : IsPGroup p P) (hPH : P ≤ H)
    (hCH : Subgroup.centralizer (P : Set G) ≤ H) (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (B : Subalgebra.center k (MonoidAlgebra k G)) {b : Subalgebra.center k (MonoidAlgebra k H)}
    (hb : IsBlockIdempotent b) :
    ∃ B', IsInducedBlock k H.subtype H.subtype_injective b B' ∧
      ∀ hB' : IsBlockIdempotent B',
        hb.centralCharacter (centerBrauerProjection hCH hHN B) = hB'.centralCharacter B := by
  classical
  obtain ⟨D, hD⟩ := exists_isDefectGroup p (e := (b : MonoidAlgebra k H))
    fun h => hb.ne_zero (Subtype.ext h)
  have : (P.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPH).2 hHN
  have hP' : IsPGroup p (P.subgroupOf H) := hP.comap_of_injective H.subtype H.subtype_injective
  have hPD := hb.le_of_isDefectGroup_of_isPGroup_of_normal hP' hD
  -- Elements of `H` centralizing `D` centralize `P`.
  have hcen : ∀ c : H, c ∈ Subgroup.centralizer (D : Set H) →
      (c : G) ∈ Subgroup.centralizer (P : Set G) := fun c hc =>
    Subgroup.mem_centralizer_iff.2 fun x hx =>
      congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hc ⟨x, hPH hx⟩
        (hPD (show (⟨x, hPH hx⟩ : H) ∈ P.subgroupOf H from hx)))
  have hCD : Subgroup.centralizer ((D.map H.subtype : Subgroup G) : Set G) ≤ H.subtype.range := by
    intro g hg
    have hgP : g ∈ Subgroup.centralizer (P : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun x hx =>
        Subgroup.mem_centralizer_iff.1 hg x ⟨⟨x, hPH hx⟩,
          hPD (show (⟨x, hPH hx⟩ : H) ∈ P.subgroupOf H from hx), rfl⟩
    exact ⟨⟨g, hCH hgP⟩, rfl⟩
  obtain ⟨B', hB'⟩ := hb.exists_isInducedBlock hb.centralCharacter_self hD hCD
  refine ⟨B', hB', fun hB'b => ?_⟩
  rw [hB'.apply_eq hb.centralCharacter_self hB'b.centralCharacter_self B, ← sub_eq_zero,
    ← map_sub]
  refine hb.apply_eq_zero_of_brauerProjection_eq_zero hb.centralCharacter_self hD ?_
  rw [brauerProjection_eq_zero_iff]
  intro c hc
  simp only [Subalgebra.coe_sub, coe_centerBrauerProjection, coe_centerRestrict, coeff_sub,
    Finsupp.coe_sub, Pi.sub_apply, coeff_mapDomainRingHom_inclusion_brauerProjection,
    coeff_restrictCoeff, Subgroup.coe_subtype, hcen c hc, ↓reduceIte, sub_self]

/-- **`Br_P(e_B)` absorbs the blocks inducing `B`** (Martínez, Theorem 4.5, p. 26). Let `P` be a
`p`-subgroup of `G`, `P C_G(P) ≤ H ≤ N_G(P)`, and `k` algebraically closed of characteristic
`p`. If `b^G = B`, then `Br_P(e_B) e_b = e_b`. -/
theorem IsInducedBlock.centerBrauerProjection_mul [IsAlgClosed k] (hP : IsPGroup p P)
    (hPH : P ≤ H) (hCH : Subgroup.centralizer (P : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G)) {B : Subalgebra.center k (MonoidAlgebra k G)}
    {b : Subalgebra.center k (MonoidAlgebra k H)}
    (h : IsInducedBlock k H.subtype H.subtype_injective b B) :
    centerBrauerProjection hCH hHN B * b = b := by
  have hb := h.isBlockIdempotent_left
  have hB := h.isBlockIdempotent_right
  obtain ⟨B', hB', hchar⟩ :=
    hb.exists_isInducedBlock_centralCharacter_centerBrauerProjection hP hPH hCH hHN B
  obtain rfl := hB'.unique h
  have h1 := hchar hB
  rw [hB.centralCharacter_self] at h1
  rw [mul_comm]
  refine ((hb.mul_eq_zero_or_eq_of_commute
    (isIdempotentElem_centerBrauerProjection hP hCH hHN hB.isIdempotentElem)
    (Commute.all _ _)).resolve_left fun h0 => ?_)
  have := congrArg hb.centralCharacter h0
  rw [map_mul, hb.centralCharacter_self, h1, mul_one, map_zero] at this
  exact one_ne_zero this

/-- **`Br_P(e_B)` kills the blocks not inducing `B`** (Martínez, Theorem 4.5, p. 26). Let `P` be
a `p`-subgroup of `G`, `P C_G(P) ≤ H ≤ N_G(P)`, and `k` algebraically closed of characteristic
`p`. If `e_b` is a block idempotent of `k[H]` with `b^G ≠ B`, then `Br_P(e_B) e_b = 0`. -/
theorem IsBlockIdempotent.centerBrauerProjection_mul_eq_zero [IsAlgClosed k] (hP : IsPGroup p P)
    (hPH : P ≤ H) (hCH : Subgroup.centralizer (P : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G)) {B : Subalgebra.center k (MonoidAlgebra k G)}
    (hB : IsBlockIdempotent B) {b : Subalgebra.center k (MonoidAlgebra k H)}
    (hb : IsBlockIdempotent b) (h : ¬IsInducedBlock k H.subtype H.subtype_injective b B) :
    centerBrauerProjection hCH hHN B * b = 0 := by
  obtain ⟨B', hB', hchar⟩ :=
    hb.exists_isInducedBlock_centralCharacter_centerBrauerProjection hP hPH hCH hHN B
  have hB'b := hB'.isBlockIdempotent_right
  have hne : B' ≠ B := fun hBB => h (hBB ▸ hB')
  have h0 := hchar hB'b
  rw [hB'b.apply_eq_zero_of_ne hB hB'b.centralCharacter_self hne] at h0
  rw [mul_comm]
  refine ((hb.mul_eq_zero_or_eq_of_commute
    (isIdempotentElem_centerBrauerProjection hP hCH hHN hB.isIdempotentElem)
    (Commute.all _ _)).resolve_right fun h1 => ?_)
  have := congrArg hb.centralCharacter h1
  rw [map_mul, hb.centralCharacter_self, h0, mul_zero] at this
  exact zero_ne_one this

/-- **Brauer's formula for `Br_P(e_B)`** (Martínez, Theorem 4.5 and Corollary 4.6, p. 26). Let `P`
be a `p`-subgroup of `G`, `P C_G(P) ≤ H ≤ N_G(P)`, `k` algebraically closed of characteristic
`p`, and `e_B` a block idempotent of `k[G]`. For a complete family `(e_i)` of block idempotents
of `k[H]`, `Br_P(e_B) = ∑_{b_i^G = B} e_i`. -/
theorem IsBlockIdempotent.centerBrauerProjection_eq_sum [IsAlgClosed k] (hP : IsPGroup p P)
    (hPH : P ≤ H) (hCH : Subgroup.centralizer (P : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G)) {B : Subalgebra.center k (MonoidAlgebra k G)}
    (hB : IsBlockIdempotent B) {ι : Type*} [Fintype ι]
    {e : ι → Subalgebra.center k (MonoidAlgebra k H)} (he : CompleteOrthogonalIdempotents e)
    (hbl : ∀ i, IsBlockIdempotent (e i))
    [DecidablePred fun i => IsInducedBlock k H.subtype H.subtype_injective (e i) B] :
    centerBrauerProjection hCH hHN B =
      ∑ i with IsInducedBlock k H.subtype H.subtype_injective (e i) B, e i := by
  rw [← mul_one (centerBrauerProjection hCH hHN B), ← he.complete, Finset.mul_sum,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · exact hi.centerBrauerProjection_mul hP hPH hCH hHN
  · exact hB.centerBrauerProjection_mul_eq_zero hP hPH hCH hHN (hbl i) hi

/-- **Brauer's formula at the normalizer** (Martínez, Theorem 4.5 and Corollary 4.6, p. 26): for
a `p`-subgroup `P` of `G` and `k` algebraically closed of characteristic `p`, the Brauer
correspondent `Br_P(e_B) ∈ k[N_G(P)]` of a block idempotent `e_B` of `k[G]` is the sum of the
block idempotents `e_b` of `k[N_G(P)]` with `b^G = B`. -/
theorem IsBlockIdempotent.brauerCorrespondent_eq_sum [IsAlgClosed k] (hP : IsPGroup p P)
    {B : Subalgebra.center k (MonoidAlgebra k G)} (hB : IsBlockIdempotent B) {ι : Type*}
    [Fintype ι] {e : ι → Subalgebra.center k (MonoidAlgebra k (Subgroup.normalizer (P : Set G)))}
    (he : CompleteOrthogonalIdempotents e) (hbl : ∀ i, IsBlockIdempotent (e i))
    [DecidablePred fun i => IsInducedBlock k (Subgroup.normalizer (P : Set G)).subtype
      (Subgroup.normalizer (P : Set G)).subtype_injective (e i) B] :
    brauerCorrespondent P (B : MonoidAlgebra k G) =
      ∑ i with IsInducedBlock k (Subgroup.normalizer (P : Set G)).subtype
        (Subgroup.normalizer (P : Set G)).subtype_injective (e i) B,
        (e i : MonoidAlgebra k (Subgroup.normalizer (P : Set G))) := by
  have := congrArg Subtype.val (hB.centerBrauerProjection_eq_sum hP Subgroup.le_normalizer
    (Subgroup.centralizer_le_normalizer (P : Set G)) le_rfl he hbl)
  rw [coe_centerBrauerProjection] at this
  rw [brauerCorrespondent_apply, this, AddSubmonoidClass.coe_finsetSum]

/-- **Defect groups of the blocks inducing `B`.** Let `P` be a defect group of a block `B` of
`k[G]`, `k` a field of characteristic `p`, and `P C_G(P) ≤ H ≤ N_G(P)`. Every block `b` of
`k[H]` with `b^G = B` has defect group `P`: it contains the normal `p`-subgroup `P` of `H`
(`TauCeti.IsBlockIdempotent.le_of_isDefectGroup_of_isPGroup_of_normal`) and lies in a defect group
of `B` (`TauCeti.IsInducedBlock.exists_isDefectGroup_le`), which is conjugate to `P`. -/
theorem IsInducedBlock.isDefectGroup_subgroupOf (hPH : P ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G)) {B : Subalgebra.center k (MonoidAlgebra k G)}
    {b : Subalgebra.center k (MonoidAlgebra k H)}
    (h : IsInducedBlock k H.subtype H.subtype_injective b B)
    (hP : IsDefectGroup k p (B : MonoidAlgebra k G) P) :
    IsDefectGroup k p (b : MonoidAlgebra k H) (P.subgroupOf H) := by
  have hb := h.isBlockIdempotent_left
  obtain ⟨D, hD⟩ := exists_isDefectGroup p (e := (b : MonoidAlgebra k H))
    fun h => hb.ne_zero (Subtype.ext h)
  have : (P.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPH).2 hHN
  have hP' : IsPGroup p (P.subgroupOf H) :=
    hP.isPGroup.comap_of_injective H.subtype H.subtype_injective
  have hPD := hb.le_of_isDefectGroup_of_isPGroup_of_normal hP' hD
  obtain ⟨E, hE, hDE⟩ := h.exists_isDefectGroup_le hD
  obtain ⟨g, rfl⟩ := h.isBlockIdempotent_right.isDefectGroup_conj hP hE
  have hcardP : Nat.card (P.subgroupOf H) = Nat.card P := by
    rw [← Subgroup.card_map_of_injective H.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 hPH]
  have hcard : Nat.card D ≤ Nat.card (P.subgroupOf H) := by
    rw [hcardP, ← Subgroup.card_map_of_injective H.subtype_injective, ← card_conj_smul_eq g P]
    exact Subgroup.card_le_of_le hDE
  rwa [← Subgroup.eq_of_le_of_card_ge hPD hcard] at hD

end BrauerFormula

end TauCeti
