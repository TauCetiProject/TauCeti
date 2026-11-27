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

The basic tool is that a central character only sees the centralizer of a defect group
(`TauCeti.IsBlockIdempotent.apply_eq_zero_of_brauerProjection_eq_zero`).

## Main results

* `TauCeti.IsBlockIdempotent.exists_isInducedBlock`: `b^G` is defined for a block `b` with a
  central character and a defect group `D` with `C_G(D) ≤ H` (Sambale, Proposition 1.11, p. 16):
  for central `z, w` the elements `(z w)_H` and `z_H w_H` agree on `C_H(D)`
  (`TauCeti.coeff_restrictCoeff_mul_of_mem_centralizer`).
* `TauCeti.IsInducedBlock.unique`, `TauCeti.IsInducedBlock.iff_centralCharacter`: uniqueness of
  `b^G`, and the defining relation for the central characters over an algebraically closed field.
* `TauCeti.IsInducedBlock.exists_isDefectGroup_le`: every defect group of `b` lies in a defect
  group of `b^G` (Sambale, Proposition 1.11, p. 16).
* `TauCeti.IsInducedBlock.trans`, `TauCeti.IsInducedBlock.of_comp`: block induction is
  transitive.
* `TauCeti.IsBlockIdempotent.centerBrauerProjection_eq_sum`: for a `p`-subgroup `P` with
  `P C_G(P) ≤ H ≤ N_G(P)` and `k` algebraically closed, `Br_P(e_B) = ∑_{b^G = B} e_b` (Martínez,
  Theorem 4.5 and Corollary 4.6, p. 26); `TauCeti.IsBlockIdempotent.brauerCorrespondent_eq_sum`
  is the case `H = N_G(P)`.
* `TauCeti.IsInducedBlock.isDefectGroup_subgroupOf`: if `P` is a defect group of `B` and
  `P ≤ H ≤ N_G(P)`, every block `b` of `k[H]` with `b^G = B` has defect group `P`.

Together, over an algebraically closed field, the last two results say that `Br_D(e_B)`, for a
block `B` with defect group `D`, is a sum of blocks of `k[N_G(D)]` with defect group `D` inducing
`B`.

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

/-- Restriction of coefficients along the identity is the identity. -/
@[simp]
theorem restrictCoeff_id (x : MonoidAlgebra k G) :
    restrictCoeff (MonoidHom.id G) Function.injective_id x = x := by
  ext
  simp

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
  ext h
  rw [coeff_restrictCoeff, one_def, one_def, coeff_single, coeff_single, ← map_one f,
    Finsupp.single_apply_left hf]

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

/-- Restriction on centres along the identity is the identity. -/
@[simp]
theorem centerRestrict_id (z : Subalgebra.center k (MonoidAlgebra k G)) :
    centerRestrict (MonoidHom.id G) Function.injective_id z = z :=
  Subtype.ext (restrictCoeff_id _)

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

section Multiplicative

variable {k G H : Type*} [CommSemiring k] [Group G] [Group H] [Finite G] {p : ℕ} [Fact p.Prime]
  [CharP k p]

/-- **Restriction is multiplicative on the centralizer of a `p`-subgroup.** Let `f : H →* G` be
injective, `G` finite, `D` a `p`-subgroup of `H` with `C_G(f(D)) ≤ f(H)`, and `k` of
characteristic `p`. For central `z, w ∈ k[G]` and `x ∈ C_H(D)`, the coefficients of `(z w)_H` and
`z_H w_H` at `x` agree. -/
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
  -- The coefficient of `(z w)_H` at `x` is `∑_{a ∈ G} z_a w_{a⁻¹ f(x)}`, that of `z_H w_H` the
  -- same sum over `a ∈ f(H)`. Both summands are invariant under conjugation by the `p`-group
  -- `f(D)`, which fixes `f(x)`, so both sums are their sums over `C_G(f(D)) ≤ f(H)`.
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

omit [Finite G] in
/-- Unfolding `TauCeti.IsInducedBlock`: `b^G = B` when `e_b`, `e_B` are block idempotents with
characters `φ`, `ψ`, `φ(e_b) = 1`, `ψ(e_B) = 1`, such that `ψ(z) = φ(z_H)` for every `z`. -/
theorem isInducedBlock_iff {f : H →* G} {hf : Function.Injective f}
    {b : Subalgebra.center k (MonoidAlgebra k H)} {B : Subalgebra.center k (MonoidAlgebra k G)} :
    IsInducedBlock k f hf b B ↔ IsBlockIdempotent b ∧ IsBlockIdempotent B ∧
      ∃ (φ : Subalgebra.center k (MonoidAlgebra k H) →ₐ[k] k)
        (ψ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k),
        φ b = 1 ∧ ψ B = 1 ∧ ∀ z, ψ z = φ (centerRestrict f hf z) :=
  Iff.rfl

namespace IsInducedBlock

variable {f : H →* G} {hf : Function.Injective f} {b : Subalgebra.center k (MonoidAlgebra k H)}
  {B : Subalgebra.center k (MonoidAlgebra k G)}

omit [Finite G] in
/-- **Constructing an induced block.** If `e_b`, `e_B` are block idempotents and `φ`, `ψ` are
characters with `φ(e_b) = 1`, `ψ(e_B) = 1` and `ψ(z) = φ(z_H)` for every `z`, then `b^G = B`. -/
theorem of_apply_eq (hb : IsBlockIdempotent b) (hB : IsBlockIdempotent B)
    {φ : Subalgebra.center k (MonoidAlgebra k H) →ₐ[k] k}
    {ψ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k} (hφ : φ b = 1) (hψ : ψ B = 1)
    (h : ∀ z, ψ z = φ (centerRestrict f hf z)) : IsInducedBlock k f hf b B :=
  ⟨hb, hB, φ, ψ, hφ, hψ, h⟩

omit [Finite G] in
/-- An induced block is a block of `k[H]`. -/
theorem isBlockIdempotent_left (h : IsInducedBlock k f hf b B) : IsBlockIdempotent b :=
  h.1

omit [Finite G] in
/-- The induced block is a block of `k[G]`. -/
theorem isBlockIdempotent_right (h : IsInducedBlock k f hf b B) : IsBlockIdempotent B :=
  h.2.1

omit [Finite G] in
/-- If `b^G = B`, there are characters `φ` of `Z(k[H])` and `ψ` of `Z(k[G])` with `φ(e_b) = 1`,
`ψ(e_B) = 1` and `ψ(z) = φ(z_H)` for every `z`. -/
theorem exists_algHom (h : IsInducedBlock k f hf b B) :
    ∃ (φ : Subalgebra.center k (MonoidAlgebra k H) →ₐ[k] k)
      (ψ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k),
      φ b = 1 ∧ ψ B = 1 ∧ ∀ z, ψ z = φ (centerRestrict f hf z) :=
  h.2.2

/-- **The defining relation, for any choice of characters.** If `b^G = B`, then for all
`k`-algebra homomorphisms `φ : Z(k[H]) → k` and `ψ : Z(k[G]) → k` with `φ(e_b) = 1` and
`ψ(e_B) = 1`, `ψ(z) = φ(z_H)`. -/
theorem apply_eq (h : IsInducedBlock k f hf b B)
    {φ : Subalgebra.center k (MonoidAlgebra k H) →ₐ[k] k}
    {ψ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k} (hφ : φ b = 1) (hψ : ψ B = 1)
    (z : Subalgebra.center k (MonoidAlgebra k G)) : ψ z = φ (centerRestrict f hf z) := by
  have : Finite H := Finite.of_injective f hf
  obtain ⟨φ', ψ', hφ', hψ', hrel⟩ := h.exists_algHom
  rw [h.isBlockIdempotent_right.algHom_ext hψ hψ', h.isBlockIdempotent_left.algHom_ext hφ hφ',
    hrel]

/-- **Uniqueness of the induced block.** `b^G`, when defined, is unique. -/
theorem unique {B' : Subalgebra.center k (MonoidAlgebra k G)} (h : IsInducedBlock k f hf b B)
    (h' : IsInducedBlock k f hf b B') : B = B' := by
  obtain ⟨φ, ψ, hφ, hψ, hrel⟩ := h.exists_algHom
  obtain ⟨-, ψ', -, hψ', -⟩ := h'.exists_algHom
  exact h.isBlockIdempotent_right.eq_of_apply_eq_one ψ h'.isBlockIdempotent_right hψ
    (by rw [hrel, ← h'.apply_eq hφ hψ', hψ'])

/-- **Transitivity of block induction.** For injective `f₁ : K →* H` and `f₂ : H →* G`, if
`b^H = c` and `c^G = B`, then `b^G = B` along `f₂ ∘ f₁`. -/
theorem trans {K : Type*} [Group K] {f₁ : K →* H} {hf₁ : Function.Injective f₁}
    {b : Subalgebra.center k (MonoidAlgebra k K)} {c : Subalgebra.center k (MonoidAlgebra k H)}
    (h₁ : IsInducedBlock k f₁ hf₁ b c) (h₂ : IsInducedBlock k f hf c B) :
    IsInducedBlock k (f.comp f₁) (hf.comp hf₁) b B := by
  have : Finite H := Finite.of_injective f hf
  obtain ⟨φ, χ, hφ, hχ, hrel₁⟩ := h₁.exists_algHom
  obtain ⟨-, ψ, -, hψ, -⟩ := h₂.exists_algHom
  refine of_apply_eq h₁.isBlockIdempotent_left h₂.isBlockIdempotent_right hφ hψ fun z => ?_
  rw [h₂.apply_eq hχ hψ, hrel₁, centerRestrict_comp]

/-- **Block induction in stages.** For injective `f₁ : K →* H` and `f₂ : H →* G`, if `b^H = c`
and `b^G = B` along `f₂ ∘ f₁`, then `c^G = B`. -/
theorem of_comp {K : Type*} [Group K] {f₁ : K →* H} {hf₁ : Function.Injective f₁}
    {b : Subalgebra.center k (MonoidAlgebra k K)} {c : Subalgebra.center k (MonoidAlgebra k H)}
    (h₁ : IsInducedBlock k f₁ hf₁ b c) (h : IsInducedBlock k (f.comp f₁) (hf.comp hf₁) b B) :
    IsInducedBlock k f hf c B := by
  have : Finite K := Finite.of_injective _ (hf.comp hf₁)
  obtain ⟨φ, χ, hφ, hχ, hrel₁⟩ := h₁.exists_algHom
  obtain ⟨-, ψ, -, hψ, -⟩ := h.exists_algHom
  refine of_apply_eq h₁.isBlockIdempotent_right h.isBlockIdempotent_right hχ hψ fun z => ?_
  rw [h.apply_eq hφ hψ, hrel₁, centerRestrict_comp]

/-- **The defining relation for central characters.** Over an algebraically closed field,
`b^G = B` exactly when `λ_B(z) = λ_b(z_H)` for every `z ∈ Z(k[G])`. -/
theorem iff_centralCharacter [Finite H] [IsAlgClosed k] (hb : IsBlockIdempotent b)
    (hB : IsBlockIdempotent B) :
    IsInducedBlock k f hf b B ↔
      ∀ z, hB.centralCharacter z = hb.centralCharacter (centerRestrict f hf z) :=
  ⟨fun h => h.apply_eq hb.centralCharacter_self hB.centralCharacter_self,
    of_apply_eq hb hB hb.centralCharacter_self hB.centralCharacter_self⟩

variable {p : ℕ} [Fact p.Prime] [CharP k p]

/-- **Defect groups grow under block induction** (Sambale, Proposition 1.11, p. 16). If
`b^G = B` along `f : H →* G` and `D` is a defect group of `b`, then `f(D)` lies in a defect group
of `B`. -/
theorem exists_isDefectGroup_le (h : IsInducedBlock k f hf b B) {D : Subgroup H}
    (hD : IsDefectGroup k p (b : MonoidAlgebra k H) D) :
    ∃ E, IsDefectGroup k p (B : MonoidAlgebra k G) E ∧ D.map f ≤ E := by
  classical
  have := Fintype.ofFinite G
  have : Finite H := Finite.of_injective f hf
  obtain ⟨φ, ψ, hφ, hψ, hrel⟩ := h.exists_algHom
  -- `λ_B(K_C) ≠ 0` for a defect class `C` of `B`, so `λ_b((K_C)_H) ≠ 0` and `(K_C)_H` has a
  -- nonzero coefficient at some `c ∈ C_H(D)`.
  obtain ⟨C, hC⟩ := exists_isDefectClass hψ
  have hψC := hC.apply_classSumCenter_ne_zero
  rw [hrel] at hψC
  have hBr := mt (h.isBlockIdempotent_left.apply_eq_zero_of_brauerProjection_eq_zero hφ hD) hψC
  rw [brauerProjection_eq_zero_iff, not_forall] at hBr
  obtain ⟨c, hc⟩ := hBr
  rw [Classical.not_imp] at hc
  obtain ⟨hc, hcC⟩ := hc
  rw [coe_centerRestrict, coeff_restrictCoeff, classSumCenter_coe, classSum_coeff] at hcC
  have hyC : ConjClasses.mk (f c) = C := by
    by_contra hne
    simp [hne] at hcC
  subst hyC
  -- `f(D)` centralizes `f c`, so lies in a Sylow `p`-subgroup of `C_G(f c)`, a defect group.
  have hDy : D.map f ≤ Subgroup.centralizer {f c} := by
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Commute.map (Subgroup.mem_centralizer_iff.1 hc d hd) f
  obtain ⟨S, hS⟩ := ((hD.isPGroup.map f).comap_of_injective _
    (Subgroup.subtype_injective (Subgroup.centralizer {f c}))).exists_le_sylow
  exact ⟨_, hC.isDefectGroup_map_sylow h.isBlockIdempotent_right hψ S,
    fun d hd => ⟨⟨d, hDy hd⟩, hS hd, rfl⟩⟩

omit [Finite G] in
/-- **Induction along the identity.** A block with a central character induces itself along the
identity of `H`. -/
theorem _root_.TauCeti.IsBlockIdempotent.isInducedBlock_id
    {b : Subalgebra.center k (MonoidAlgebra k H)} (hb : IsBlockIdempotent b)
    {φ : Subalgebra.center k (MonoidAlgebra k H) →ₐ[k] k} (hφ : φ b = 1) :
    IsInducedBlock k (MonoidHom.id H) Function.injective_id b b :=
  of_apply_eq hb hb hφ hφ fun z => by rw [centerRestrict_id]

end IsInducedBlock

end Induction

section Existence

variable {k G H : Type*} [Field k] [Group G] [Group H] [Finite G] {p : ℕ}
  [Fact p.Prime] [CharP k p] {f : H →* G} {hf : Function.Injective f}
  {φ : Subalgebra.center k (MonoidAlgebra k H) →ₐ[k] k}
  {b : Subalgebra.center k (MonoidAlgebra k H)} {D : Subgroup H}

/-- **Restriction is multiplicative under a central character.** Let `e_b` be a block idempotent
of `k[H]` with a `k`-algebra homomorphism `φ : Z(k[H]) → k`, `φ(e_b) = 1`, and a defect group `D`
with `C_G(f(D)) ≤ f(H)`. Then `z ↦ φ(z_H)` is multiplicative on `Z(k[G])`. -/
theorem IsBlockIdempotent.apply_centerRestrict_mul (hb : IsBlockIdempotent b) (hφ : φ b = 1)
    (hD : IsDefectGroup k p (b : MonoidAlgebra k H) D)
    (hC : Subgroup.centralizer ((D.map f : Subgroup G) : Set G) ≤ f.range)
    (z w : Subalgebra.center k (MonoidAlgebra k G)) :
    φ (centerRestrict f hf (z * w)) = φ (centerRestrict f hf z) * φ (centerRestrict f hf w) := by
  have : Finite H := Finite.of_injective f hf
  -- `(z w)_H - z_H w_H` has no coefficient on `C_H(D)`, so `φ` kills it.
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
`C_G(f(D)) ≤ f(H)`. Then `b^G` is defined. -/
theorem IsBlockIdempotent.exists_isInducedBlock (hb : IsBlockIdempotent b) (hφ : φ b = 1)
    (hD : IsDefectGroup k p (b : MonoidAlgebra k H) D)
    (hC : Subgroup.centralizer ((D.map f : Subgroup G) : Set G) ≤ f.range) :
    ∃ B, IsInducedBlock k f hf b B := by
  -- `z ↦ φ(z_H)` is a `k`-algebra homomorphism, so the character of exactly one block of `k[G]`.
  let ψ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k :=
    AlgHom.ofLinearMap (φ.toLinearMap ∘ₗ centerRestrict f hf) (by simp)
      (hb.apply_centerRestrict_mul hφ hD hC)
  obtain ⟨B, ⟨hB, hψ⟩, -⟩ := existsUnique_isBlockIdempotent_apply_eq_one ψ
  exact ⟨B, IsInducedBlock.of_apply_eq hb hB hφ hψ fun _ => rfl⟩

end Existence

section BrauerFormula

variable {k G : Type*} [Field k] [Group G] [Finite G] {P H : Subgroup G} {p : ℕ} [Fact p.Prime]
  [CharP k p]

/-- Let `P` be a `p`-subgroup of `G`, `P C_G(P) ≤ H ≤ N_G(P)`, `k` a field of characteristic `p`,
and `e_b` a block idempotent of `k[H]` with a character `φ : Z(k[H]) → k`, `φ(e_b) = 1`. Then `b`
induces a block `B'` of `k[G]`, and `φ(Br_P(e_B)) = ψ(e_B)` for every block `B` of `k[G]` and
every character `ψ` of `Z(k[G])` with `ψ(e_{B'}) = 1`. -/
theorem IsBlockIdempotent.exists_isInducedBlock_apply_centerBrauerProjection (hP : IsPGroup p P)
    (hPH : P ≤ H) (hCH : Subgroup.centralizer (P : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G)) {b : Subalgebra.center k (MonoidAlgebra k H)}
    (hb : IsBlockIdempotent b) {φ : Subalgebra.center k (MonoidAlgebra k H) →ₐ[k] k}
    (hφ : φ b = 1) :
    ∃ B', IsInducedBlock k H.subtype H.subtype_injective b B' ∧
      ∀ ψ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k, ψ B' = 1 →
        ∀ B, φ (centerBrauerProjection hCH hHN B) = ψ B := by
  classical
  obtain ⟨D, hD⟩ := exists_isDefectGroup p (e := (b : MonoidAlgebra k H))
    fun h => hb.ne_zero (Subtype.ext h)
  -- `P ≤ D`, so elements centralizing `D` centralize `P`.
  have hPD : P ≤ D.map H.subtype := by
    simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPH] using
      Subgroup.map_mono (f := H.subtype) (hb.subgroupOf_le_of_isDefectGroup hP hPH hHN hD)
  have hCP : Subgroup.centralizer ((D.map H.subtype : Subgroup G) : Set G) ≤
      Subgroup.centralizer (P : Set G) :=
    Subgroup.centralizer_le hPD
  obtain ⟨B', hB'⟩ := hb.exists_isInducedBlock hφ hD fun g hg => ⟨⟨g, hCH (hCP hg)⟩, rfl⟩
  refine ⟨B', hB', fun ψ hψ B => ?_⟩
  -- `Br_P(e_B)` and `(e_B)_H` agree on `C_H(D) ≤ C_G(P)`, so `φ` takes the same value on them.
  rw [hB'.apply_eq hφ hψ B, ← sub_eq_zero, ← map_sub]
  refine hb.apply_eq_zero_of_brauerProjection_eq_zero hφ hD ?_
  rw [brauerProjection_eq_zero_iff]
  intro c hc
  have hcP : (c : G) ∈ Subgroup.centralizer (P : Set G) :=
    hCP (Subgroup.map_centralizer_le_centralizer_image _ H.subtype ⟨c, hc, rfl⟩)
  simp [hcP]

/-- **`Br_P(e_B)` absorbs the blocks inducing `B`** (Martínez, Theorem 4.5, p. 26). Let `P` be a
`p`-subgroup of `G`, `P C_G(P) ≤ H ≤ N_G(P)`, and `k` a field of characteristic `p`. If
`b^G = B`, then `Br_P(e_B) e_b = e_b`. -/
theorem IsInducedBlock.centerBrauerProjection_mul_eq_right (hP : IsPGroup p P) (hPH : P ≤ H)
    (hCH : Subgroup.centralizer (P : Set G) ≤ H) (hHN : H ≤ Subgroup.normalizer (P : Set G))
    {B : Subalgebra.center k (MonoidAlgebra k G)} {b : Subalgebra.center k (MonoidAlgebra k H)}
    (h : IsInducedBlock k H.subtype H.subtype_injective b B) :
    centerBrauerProjection hCH hHN B * b = b := by
  have hb := h.isBlockIdempotent_left
  have hB := h.isBlockIdempotent_right
  obtain ⟨φ, ψ, hφ, hψ, -⟩ := h.exists_algHom
  obtain ⟨B', hB', hchar⟩ :=
    hb.exists_isInducedBlock_apply_centerBrauerProjection hP hPH hCH hHN hφ
  have h1 := hchar ψ (by rw [hB'.unique h, hψ]) B
  rw [hψ] at h1
  rw [mul_comm]
  refine ((hb.mul_eq_zero_or_eq_of_commute
    (isIdempotentElem_centerBrauerProjection hCH hHN hP hB.isIdempotentElem)
    (Commute.all _ _)).resolve_left fun h0 => ?_)
  have := congrArg φ h0
  rw [map_mul, hφ, h1, mul_one, map_zero] at this
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
    hb.exists_isInducedBlock_apply_centerBrauerProjection hP hPH hCH hHN hb.centralCharacter_self
  have hB'b := hB'.isBlockIdempotent_right
  have hne : B' ≠ B := fun hBB => h (hBB ▸ hB')
  have h0 := hchar _ hB'b.centralCharacter_self B
  rw [hB'b.apply_eq_zero_of_ne hB hB'b.centralCharacter_self hne] at h0
  rw [mul_comm]
  refine ((hb.mul_eq_zero_or_eq_of_commute
    (isIdempotentElem_centerBrauerProjection hCH hHN hP hB.isIdempotentElem)
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
  · exact hi.centerBrauerProjection_mul_eq_right hP hPH hCH hHN
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
    brauerCorrespondent (Subgroup.centralizer_le_normalizer (P : Set G)) (B : MonoidAlgebra k G) =
      ∑ i with IsInducedBlock k (Subgroup.normalizer (P : Set G)).subtype
        (Subgroup.normalizer (P : Set G)).subtype_injective (e i) B,
        (e i : MonoidAlgebra k (Subgroup.normalizer (P : Set G))) := by
  rw [← coe_centerBrauerProjection _ le_rfl, hB.centerBrauerProjection_eq_sum hP
    Subgroup.le_normalizer _ le_rfl he hbl, AddSubmonoidClass.coe_finsetSum]

/-- **Defect groups of the blocks inducing `B`.** Let `P` be a defect group of a block `B` of
`k[G]`, `k` a field of characteristic `p`, and `P ≤ H ≤ N_G(P)`. Every block `b` of `k[H]` with
`b^G = B` has defect group `P`. -/
theorem IsInducedBlock.isDefectGroup_subgroupOf (hPH : P ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G)) {B : Subalgebra.center k (MonoidAlgebra k G)}
    {b : Subalgebra.center k (MonoidAlgebra k H)}
    (h : IsInducedBlock k H.subtype H.subtype_injective b B)
    (hP : IsDefectGroup k p (B : MonoidAlgebra k G) P) :
    IsDefectGroup k p (b : MonoidAlgebra k H) (P.subgroupOf H) := by
  have hb := h.isBlockIdempotent_left
  obtain ⟨D, hD⟩ := exists_isDefectGroup p (e := (b : MonoidAlgebra k H))
    fun h => hb.ne_zero (Subtype.ext h)
  -- A defect group `D` of `b` contains `P` and lies in a defect group of `B`, a conjugate of `P`.
  have hPD := hb.subgroupOf_le_of_isDefectGroup hP.isPGroup hPH hHN hD
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
