/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Kummer.Degree
public import TauCeti.NumberTheory.LocalField.NormResidueSymbol.Steinberg
public import TauCeti.NumberTheory.LocalField.PowerSubgroup.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.FieldTheory.Kummer.Cyclic
import TauCeti.GroupTheory.Abelianization.Basic
import TauCeti.NumberTheory.LocalField.PowerSubgroup.Open

/-!
# Nondegeneracy and Kummer norm duality of the norm-residue symbol

Let `K` be a nonarchimedean local field containing the `n`-th roots of unity. By skew symmetry
(`TauCeti.normResidueSymbol_symm`) and the Artin norm criterion
(`TauCeti.normResidueSymbol_eq_one_iff_mem_normGroup`), the norm-residue symbol satisfies the
dual norm criterion in the radical argument as well: for `L = K(ⁿ√a)`, `(a, b) = 1` if and only if
`b ∈ N_{L/K}(Lˣ)`.

From the norm criterion in both arguments follows **nondegeneracy**
(`forall_normResidueSymbol_eq_one_iff_right`, `forall_normResidueSymbol_eq_one_iff_left`): if
`(a, b) = 1` for every `a ∈ Kˣ`, then `N_{K(ⁿ√b)/K} = Kˣ`, so `[K(ⁿ√b) : K] = 1` by local
reciprocity and `b ∈ (Kˣ)ⁿ`; skew symmetry gives the symmetric statement in the first argument.
Because `K` contains a primitive `n`-th root of unity, `(n : K) ≠ 0`, so `Kˣ ⧸ (Kˣ)ⁿ` is finite of
exponent dividing `n`. Finite abelian group duality (`Mathlib.GroupTheory.FiniteAbelian.Duality`)
then upgrades injectivity of `normResidueSymbolPairing` to the **perfect pairing isomorphism**
`normResidueSymbolPairingEquiv : Kˣ ⧸ (Kˣ)ⁿ ≃* (Kˣ ⧸ (Kˣ)ⁿ →* rootsOfUnity n K)`.

For a subgroup `B ≤ Kˣ`, its orthogonal complement `normResidueOrthogonal K n B` consists of those
`a ∈ Kˣ` with `(a, b) = 1` for all `b ∈ B` (equivalently `(b, a) = 1`). It is an open subgroup of
finite index `[Kˣ : B^⊥] = [B : B ∩ (Kˣ)ⁿ]`, and perfectness gives the double-orthogonal identity
`(B^⊥)^⊥ = B ⊔ (Kˣ)ⁿ` (`normResidueOrthogonal_normResidueOrthogonal`). Comparing `B^⊥` with the
Kummer field `K(B^{1/n})` (`TauCeti.kummerField`) proves **Fesenko–Vostokov's Kummer norm
theorem**: inside any separably closed extension `E` of `K`,

`N_{K(B^{1/n})/K}(K(B^{1/n})ˣ) = B^⊥`,

and consequently `N_{K((A^⊥)^{1/n})/K} = A` for every subgroup `A ≤ Kˣ` containing `(Kˣ)ⁿ`
(`normGroup_kummerField_normResidueOrthogonal_of_le`).

## Main definitions

* `TauCeti.normResidueSymbolPairingEquiv`: the canonical isomorphism
  `powerClassQuotient Kˣ n ≃* (powerClassQuotient Kˣ n →* rootsOfUnity n K)` induced by the
  norm-residue symbol.
* `TauCeti.normResidueOrthogonal K n B`: the orthogonal subgroup `{a ∈ Kˣ | ∀ b ∈ B, (a, b) = 1}`.

## Main results

* `TauCeti.normResidueSymbol_eq_one_iff_mem_normGroup_of_pow_eq_left`: for `L = K(s)` with
  `sⁿ = a`, `normResidueSymbol K n a b = 1 ↔ b ∈ normGroup K L`.
* `TauCeti.forall_normResidueSymbol_eq_one_iff_right`,
  `TauCeti.forall_normResidueSymbol_eq_one_iff_left`: nondegeneracy in both arguments, showing the
  left and right kernels of `normResidueSymbol K n` are `powerSubgroup Kˣ n`.
* `TauCeti.normResidueSymbolPairing_bijective`, `TauCeti.normResidueSymbolPairing_flip_bijective`:
  `normResidueSymbolPairing` and its flip are bijective.
* `TauCeti.isOpen_normResidueOrthogonal`, `TauCeti.finiteIndex_normResidueOrthogonal`,
  `TauCeti.index_normResidueOrthogonal`: `B^⊥` is an open subgroup of finite index
  `[Kˣ : B^⊥] = [B : B ∩ (Kˣ)ⁿ]`.
* `TauCeti.normResidueOrthogonal_normResidueOrthogonal`,
  `TauCeti.normResidueOrthogonal_normResidueOrthogonal_of_le`: double-orthogonal duality
  `(B^⊥)^⊥ = B ⊔ (Kˣ)ⁿ`, hence `(A^⊥)^⊥ = A` when `(Kˣ)ⁿ ≤ A`.
* `TauCeti.normGroup_kummerField_eq_normResidueOrthogonal`: `normGroup K (kummerField E n B) = B^⊥`
  when `E` is separably closed (or more generally whenever every `b ∈ B` has an `n`-th root in `E`,
  `TauCeti.normGroup_kummerField_eq_normResidueOrthogonal_of_forall_exists_pow_eq`).
* `TauCeti.normGroup_kummerField_normResidueOrthogonal_of_le`: for `(Kˣ)ⁿ ≤ A`, the Kummer
  extension `K((A^⊥)^{1/n})` has norm subgroup `A`.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, 2nd ed., AMS Translations
  of Mathematical Monographs 121 (2002), Chapter IV, §5, (5.1)(3)–(4) and (5.2) Theorem,
  pp. 143–145.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter III, §4, Theorem 4.4.
-/

public section

noncomputable section

namespace TauCeti

open ClassFieldTheory _root_.IntermediateField Module

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

/-! ### The norm criterion in the radical argument -/

/-- **The norm criterion in the radical argument.** Let `L = K(s)` be a finite radical extension
generated over `K` by an element `s ∈ L` with `sⁿ = a`. Then `(a, b) = 1` if and only if
`b ∈ N_{L/K}(Lˣ)`. -/
theorem normResidueSymbol_eq_one_iff_mem_normGroup_of_pow_eq_left {L : Type*} [Field L]
    [Algebra K L] [FiniteDimensional K L] (a b : Kˣ) {s : L} (hs : s ^ n = algebraMap K L a)
    (hgen : K⟮s⟯ = ⊤) :
    normResidueSymbol K n a b = 1 ↔ b ∈ normGroup K L :=
  (normResidueSymbol_eq_one_comm a b).trans (normResidueSymbol_eq_one_iff_mem_normGroup b a hs hgen)

/-- In any field extension `E/K` containing an `n`-th root `α` of `a`, `(a, b) = 1` holds if and
only if `b` is a unit norm from `K⟮α⟯`. -/
theorem normResidueSymbol_eq_one_iff_mem_range_normUnits_adjoin_left {E : Type*} [Field E]
    [Algebra K E] (a b : Kˣ) {α : E} (hα : α ^ n = algebraMap K E a) :
    normResidueSymbol K n a b = 1 ↔ b ∈ (Algebra.normUnits K : K⟮α⟯ˣ →* Kˣ).range :=
  (normResidueSymbol_eq_one_comm a b).trans
    (normResidueSymbol_eq_one_iff_mem_range_normUnits_adjoin b a hα)

/-! ### Nondegeneracy and perfectness of the norm-residue pairing -/

/-- **Nondegeneracy of the norm-residue symbol in the radical argument.** An element `b ∈ Kˣ` pairs
to `1` on the right with every `a ∈ Kˣ` if and only if `b ∈ (Kˣ)ⁿ`. -/
theorem forall_normResidueSymbol_eq_one_iff_right (b : Kˣ) :
    (∀ a : Kˣ, normResidueSymbol K n a b = 1) ↔ b ∈ powerSubgroup Kˣ n := by
  refine ⟨fun h ↦ ?_, fun hb a ↦ normResidueSymbol_eq_one_of_mem_powerSubgroup_right a hb⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K n
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) b)
    (NeZero.pos n)
  have : FiniteDimensional K K⟮s⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral s)
  have ht : AdjoinSimple.gen K s ^ n = algebraMap K K⟮s⟯ b := Subtype.ext (by simpa using hs)
  have htop := adjoin_adjoinSimple_gen_eq_top (F := K) s
  have hnorm : normGroup K K⟮s⟯ = ⊤ :=
    eq_top_iff.2 fun a _ ↦ (normResidueSymbol_eq_one_iff_mem_normGroup a b ht htop).1 (h a)
  have := isGalois_of_pow_eq_of_adjoin_eq_top hζ ht htop
  have := isCyclic_of_pow_eq_of_adjoin_eq_top hζ ht htop
  let _ : CommGroup Gal(K⟮s⟯/K) := IsCyclic.commGroup
  have h1 : finrank K K⟮s⟯ = 1 := by
    rw [← index_normGroup_of_isMulCommutative K K⟮s⟯, hnorm, Subgroup.index_top]
  obtain ⟨c, hc⟩ := mem_bot.1 (adjoin_simple_eq_bot_iff.1 (finrank_eq_one_iff.1 h1))
  have hcb : c ^ n = b := (algebraMap K (AlgebraicClosure K)).injective (by rw [map_pow, hc, hs])
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact b.ne_zero (by rw [← hcb, zero_pow (NeZero.ne n)])
  exact (mem_powerSubgroup_iff n).2 ⟨Units.mk0 c hc0, Units.ext (by simpa using hcb)⟩

/-- **Nondegeneracy of the norm-residue symbol in the Artin argument.** An element `a ∈ Kˣ` pairs to
`1` on the left with every `b ∈ Kˣ` if and only if `a ∈ (Kˣ)ⁿ`. -/
theorem forall_normResidueSymbol_eq_one_iff_left (a : Kˣ) :
    (∀ b : Kˣ, normResidueSymbol K n a b = 1) ↔ a ∈ powerSubgroup Kˣ n := by
  simp_rw [normResidueSymbol_eq_one_comm a, forall_normResidueSymbol_eq_one_iff_right]

/-- `normResidueSymbolPairing` is injective on `Kˣ ⧸ (Kˣ)ⁿ`. -/
theorem normResidueSymbolPairing_injective :
    Function.Injective (normResidueSymbolPairing (K := K) (n := n)) := by
  refine (injective_iff_map_eq_one _).2 fun x hx ↦ ?_
  obtain ⟨a, rfl⟩ := powerClassHom_surjective Kˣ n x
  rw [powerClassHom_apply, QuotientGroup.eq_one_iff, ← forall_normResidueSymbol_eq_one_iff_left]
  intro b
  simpa only [powerClassHom_apply, normResidueSymbolPairing_mk, MonoidHom.one_apply] using
    DFunLike.congr_fun hx (QuotientGroup.mk b)

/-- The flipped pairing `(normResidueSymbolPairing).flip` is injective on `Kˣ ⧸ (Kˣ)ⁿ`. -/
theorem normResidueSymbolPairing_flip_injective :
    Function.Injective (normResidueSymbolPairing (K := K) (n := n)).flip := by
  refine (injective_iff_map_eq_one _).2 fun y hy ↦ ?_
  obtain ⟨b, rfl⟩ := powerClassHom_surjective Kˣ n y
  rw [powerClassHom_apply, QuotientGroup.eq_one_iff, ← forall_normResidueSymbol_eq_one_iff_right]
  intro a
  simpa only [powerClassHom_apply, MonoidHom.flip_apply, normResidueSymbolPairing_mk,
    MonoidHom.one_apply] using DFunLike.congr_fun hy (QuotientGroup.mk a)

/-- **Perfectness of the norm-residue pairing.** The homomorphism
`normResidueSymbolPairing : Kˣ ⧸ (Kˣ)ⁿ →* (Kˣ ⧸ (Kˣ)ⁿ →* rootsOfUnity n K)` is bijective. -/
theorem normResidueSymbolPairing_bijective :
    Function.Bijective (normResidueSymbolPairing (K := K) (n := n)) := by
  -- Nondegeneracy gives injectivity, and finite abelian group duality bounds the character group
  -- cardinality by `#(Kˣ ⧸ (Kˣ)ⁿ)`.
  set P := powerClassQuotient Kˣ n
  have : HasEnoughRootsOfUnity K (Monoid.exponent P) :=
    HasEnoughRootsOfUnity.of_dvd K
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.2 (powerClassQuotient_pow_eq_one n))
  let post : (P →* rootsOfUnity n K) → (P →* Kˣ) := fun φ ↦ (rootsOfUnity n K).subtype.comp φ
  have hpost : Function.Injective post := fun φ ψ h ↦
    MonoidHom.ext fun x ↦ Subtype.ext (DFunLike.congr_fun h x)
  have : Finite (P →* Kˣ) :=
    Finite.of_equiv P (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity P K).some.symm.toEquiv
  have : Finite (P →* rootsOfUnity n K) := Finite.of_injective post hpost
  refine normResidueSymbolPairing_injective.bijective_of_nat_card_le ?_
  exact (Nat.card_le_card_of_injective post hpost).trans
    (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity P K).le

/-- The flipped pairing `(normResidueSymbolPairing).flip` is bijective on `Kˣ ⧸ (Kˣ)ⁿ`. -/
theorem normResidueSymbolPairing_flip_bijective :
    Function.Bijective (normResidueSymbolPairing (K := K) (n := n)).flip := by
  have : Finite (powerClassQuotient Kˣ n →* rootsOfUnity n K) :=
    Finite.of_surjective _ normResidueSymbolPairing_bijective.surjective
  exact normResidueSymbolPairing_flip_injective.bijective_of_nat_card_le
    (Nat.card_congr (Equiv.ofBijective _ normResidueSymbolPairing_bijective)).symm.le

variable (K n) in
/-- **The norm-residue perfect pairing equivalence** identifying `Kˣ ⧸ (Kˣ)ⁿ` with its Pontryagin
dual `Kˣ ⧸ (Kˣ)ⁿ →* rootsOfUnity n K`. -/
def normResidueSymbolPairingEquiv :
    powerClassQuotient Kˣ n ≃* (powerClassQuotient Kˣ n →* rootsOfUnity n K) :=
  MulEquiv.ofBijective (normResidueSymbolPairing (K := K) (n := n))
    normResidueSymbolPairing_bijective

@[simp]
theorem normResidueSymbolPairingEquiv_apply (x : powerClassQuotient Kˣ n) :
    normResidueSymbolPairingEquiv K n x = normResidueSymbolPairing x :=
  (rfl)

/-- On classes of units, `normResidueSymbolPairingEquiv` evaluates to `normResidueSymbol`. -/
theorem normResidueSymbolPairingEquiv_mk (a b : Kˣ) :
    normResidueSymbolPairingEquiv K n (QuotientGroup.mk a) (QuotientGroup.mk b) =
      normResidueSymbol K n a b :=
  normResidueSymbolPairing_mk a b

/-! ### Orthogonal subgroups under the norm-residue symbol -/

variable (K n) in
/-- The **orthogonal subgroup** `B^⊥ ≤ Kˣ` of `B ≤ Kˣ` under the degree-`n` norm-residue symbol:
the subgroup of elements `a ∈ Kˣ` satisfying `(a, b) = 1` for all `b ∈ B`. By skew symmetry this
coincides with `{a : Kˣ | ∀ b ∈ B, (b, a) = 1}` (`mem_normResidueOrthogonal_iff_right`). -/
def normResidueOrthogonal (B : Subgroup Kˣ) : Subgroup Kˣ where
  carrier := {a : Kˣ | ∀ b ∈ B, normResidueSymbol K n a b = 1}
  one_mem' _ _ := normResidueSymbol_one_left _
  mul_mem' ha hb b hbB := by rw [normResidueSymbol_mul_left, ha b hbB, hb b hbB, mul_one]
  inv_mem' ha b hbB := by rw [normResidueSymbol_inv_left, ha b hbB, inv_one]

@[simp]
theorem mem_normResidueOrthogonal_iff {B : Subgroup Kˣ} {a : Kˣ} :
    a ∈ normResidueOrthogonal K n B ↔ ∀ b ∈ B, normResidueSymbol K n a b = 1 :=
  (Iff.rfl)

/-- Membership in `normResidueOrthogonal K n B` read in the second argument via skew symmetry. -/
theorem mem_normResidueOrthogonal_iff_right {B : Subgroup Kˣ} {a : Kˣ} :
    a ∈ normResidueOrthogonal K n B ↔ ∀ b ∈ B, normResidueSymbol K n b a = 1 := by
  simp_rw [mem_normResidueOrthogonal_iff, normResidueSymbol_eq_one_comm a]

/-- Every orthogonal subgroup contains `(Kˣ)ⁿ`. -/
theorem powerSubgroup_le_normResidueOrthogonal (B : Subgroup Kˣ) :
    powerSubgroup Kˣ n ≤ normResidueOrthogonal K n B :=
  fun _ ha b _ ↦ normResidueSymbol_eq_one_of_mem_powerSubgroup_left ha b

/-- Every orthogonal subgroup `B^⊥ ≤ Kˣ` has finite index in `Kˣ`. -/
instance finiteIndex_normResidueOrthogonal (B : Subgroup Kˣ) :
    (normResidueOrthogonal K n B).FiniteIndex := by
  have : (powerSubgroup Kˣ n).FiniteIndex := by
    rw [powerSubgroup_eq_range_powMonoidHom]
    infer_instance
  exact Subgroup.finiteIndex_of_le (powerSubgroup_le_normResidueOrthogonal B)

/-- Every orthogonal subgroup `B^⊥ ≤ Kˣ` is open in `Kˣ`. -/
theorem isOpen_normResidueOrthogonal (B : Subgroup Kˣ) :
    IsOpen (normResidueOrthogonal K n B : Set Kˣ) := by
  have hn : (n : K) ≠ 0 :=
    (HasEnoughRootsOfUnity.exists_isPrimitiveRoot K n).choose_spec.neZero'.out
  have hle : (powMonoidHom n : Kˣ →* Kˣ).range ≤ normResidueOrthogonal K n B := by
    rw [← powerSubgroup_eq_range_powMonoidHom]
    exact powerSubgroup_le_normResidueOrthogonal B
  exact Subgroup.isOpen_mono hle (isOpen_range_powMonoidHom hn)

/-- Every orthogonal subgroup `B^⊥ ≤ Kˣ` is closed in `Kˣ`. -/
theorem isClosed_normResidueOrthogonal (B : Subgroup Kˣ) :
    IsClosed (normResidueOrthogonal K n B : Set Kˣ) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_normResidueOrthogonal B)

/-- `normResidueOrthogonal K n` is antitone. -/
theorem normResidueOrthogonal_antitone : Antitone (normResidueOrthogonal K n) :=
  fun _ _ h _ ha b hb ↦ ha b (h hb)

/-- Galois connection symmetry for `normResidueOrthogonal`: `A ≤ B^⊥ ↔ B ≤ A^⊥`. -/
theorem le_normResidueOrthogonal_iff {A B : Subgroup Kˣ} :
    A ≤ normResidueOrthogonal K n B ↔ B ≤ normResidueOrthogonal K n A := by
  refine ⟨fun h b hb a ha ↦ ?_, fun h a ha b hb ↦ ?_⟩
  · exact (normResidueSymbol_eq_one_comm a b).1 (h ha b hb)
  · exact (normResidueSymbol_eq_one_comm b a).1 (h hb a ha)

/-- Every subgroup lies in its double orthogonal. -/
theorem le_normResidueOrthogonal_normResidueOrthogonal (B : Subgroup Kˣ) :
    B ≤ normResidueOrthogonal K n (normResidueOrthogonal K n B) :=
  le_normResidueOrthogonal_iff.1 le_rfl

@[simp]
theorem normResidueOrthogonal_bot : normResidueOrthogonal K n ⊥ = ⊤ := by
  ext a
  simp

@[simp]
theorem normResidueOrthogonal_top : normResidueOrthogonal K n ⊤ = powerSubgroup Kˣ n := by
  ext a
  simp [forall_normResidueSymbol_eq_one_iff_left]

@[simp]
theorem normResidueOrthogonal_powerSubgroup :
    normResidueOrthogonal K n (powerSubgroup Kˣ n) = ⊤ :=
  eq_top_iff.2 fun a _ _ hb ↦ normResidueSymbol_eq_one_of_mem_powerSubgroup_right a hb

/-- The orthogonal complement of a join of subgroups is the meet of their orthogonal complements. -/
theorem normResidueOrthogonal_sup (A B : Subgroup Kˣ) :
    normResidueOrthogonal K n (A ⊔ B) =
      normResidueOrthogonal K n A ⊓ normResidueOrthogonal K n B :=
  le_antisymm
    (le_inf (normResidueOrthogonal_antitone le_sup_left)
      (normResidueOrthogonal_antitone le_sup_right))
    (le_normResidueOrthogonal_iff.2
      (sup_le (le_normResidueOrthogonal_iff.1 inf_le_left)
        (le_normResidueOrthogonal_iff.1 inf_le_right)))

@[simp]
theorem normResidueOrthogonal_sup_powerSubgroup (B : Subgroup Kˣ) :
    normResidueOrthogonal K n (B ⊔ powerSubgroup Kˣ n) = normResidueOrthogonal K n B := by
  rw [normResidueOrthogonal_sup, normResidueOrthogonal_powerSubgroup, inf_top_eq]

/-- **Double-orthogonal theorem for the norm-residue symbol.** For every subgroup `B ≤ Kˣ`,
`(B^⊥)^⊥ = B ⊔ (Kˣ)ⁿ`. -/
theorem normResidueOrthogonal_normResidueOrthogonal (B : Subgroup Kˣ) :
    normResidueOrthogonal K n (normResidueOrthogonal K n B) = B ⊔ powerSubgroup Kˣ n := by
  refine le_antisymm (fun a ha ↦ ?_)
    (sup_le (le_normResidueOrthogonal_normResidueOrthogonal B)
      (powerSubgroup_le_normResidueOrthogonal _))
  set P := powerClassQuotient Kˣ n
  set π := powerClassHom Kˣ n
  have : HasEnoughRootsOfUnity K (Monoid.exponent P) :=
    HasEnoughRootsOfUnity.of_dvd K
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.2 (powerClassQuotient_pow_eq_one n))
  rw [← ker_powerClassHom Kˣ n, ← Subgroup.comap_map_eq, Subgroup.mem_comap,
    ← CommGroup.forall_monoidHom_apply_eq_one_iff K (B.map π)]
  intro φ hφ
  let φ₀ : P →* rootsOfUnity n K :=
    { toFun x := ⟨φ x, (mem_rootsOfUnity n (φ x)).2
        (by rw [← map_pow, powerClassQuotient_pow_eq_one, map_one])⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' x y := Subtype.ext (map_mul φ x y) }
  obtain ⟨z, hz⟩ := normResidueSymbolPairing_bijective.surjective φ₀
  obtain ⟨c, rfl⟩ := powerClassHom_surjective Kˣ n z
  have hcφ (u : Kˣ) : (normResidueSymbol K n c u : Kˣ) = φ (π u) := by
    have h := congrArg (fun r : rootsOfUnity n K ↦ (r : Kˣ)) (DFunLike.congr_fun hz (π u))
    simpa only [π, powerClassHom_apply, normResidueSymbolPairing_mk, φ₀, MonoidHom.coe_mk,
      OneHom.coe_mk] using h
  have hcB : c ∈ normResidueOrthogonal K n B := fun b hb ↦
    Subtype.ext ((hcφ b).trans (hφ (π b) (Subgroup.mem_map_of_mem π hb)))
  exact (hcφ a).symm.trans (congrArg Subtype.val ((normResidueSymbol_eq_one_comm a c).1 (ha c hcB)))

/-- For a subgroup `A ≤ Kˣ` containing `(Kˣ)ⁿ`, its double orthogonal under the norm-residue symbol
is `A` itself. -/
theorem normResidueOrthogonal_normResidueOrthogonal_of_le {A : Subgroup Kˣ}
    (hA : powerSubgroup Kˣ n ≤ A) :
    normResidueOrthogonal K n (normResidueOrthogonal K n A) = A := by
  rw [normResidueOrthogonal_normResidueOrthogonal, sup_eq_left.2 hA]

/-- Two subgroups of `Kˣ` have the same orthogonal complement under the norm-residue symbol if and
only if they generate the same subgroup modulo `(Kˣ)ⁿ`. -/
theorem normResidueOrthogonal_eq_iff {A B : Subgroup Kˣ} :
    normResidueOrthogonal K n A = normResidueOrthogonal K n B ↔
      A ⊔ powerSubgroup Kˣ n = B ⊔ powerSubgroup Kˣ n := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← normResidueOrthogonal_normResidueOrthogonal A, h,
      normResidueOrthogonal_normResidueOrthogonal]
  · rw [← normResidueOrthogonal_sup_powerSubgroup A, h, normResidueOrthogonal_sup_powerSubgroup]

/-- If `A ≤ Kˣ` contains `(Kˣ)ⁿ`, then `(A ⊓ B)^⊥ = A^⊥ ⊔ B^⊥` for every subgroup `B ≤ Kˣ`. -/
theorem normResidueOrthogonal_inf_of_le_left {A : Subgroup Kˣ} (hA : powerSubgroup Kˣ n ≤ A)
    (B : Subgroup Kˣ) :
    normResidueOrthogonal K n (A ⊓ B) =
      normResidueOrthogonal K n A ⊔ normResidueOrthogonal K n B := by
  have hmod : (A ⊓ B) ⊔ powerSubgroup Kˣ n = A ⊓ (B ⊔ powerSubgroup Kˣ n) := by
    rw [sup_comm, inf_comm A B, ← sup_inf_assoc_of_le B hA, sup_comm, inf_comm]
  rw [← normResidueOrthogonal_normResidueOrthogonal_of_le (le_trans
      (powerSubgroup_le_normResidueOrthogonal A) le_sup_left),
    normResidueOrthogonal_sup, normResidueOrthogonal_normResidueOrthogonal_of_le hA,
    normResidueOrthogonal_normResidueOrthogonal, ← hmod, normResidueOrthogonal_sup_powerSubgroup]

/-- If `B ≤ Kˣ` contains `(Kˣ)ⁿ`, then `(A ⊓ B)^⊥ = A^⊥ ⊔ B^⊥` for every subgroup `A ≤ Kˣ`. -/
theorem normResidueOrthogonal_inf_of_le_right (A : Subgroup Kˣ) {B : Subgroup Kˣ}
    (hB : powerSubgroup Kˣ n ≤ B) :
    normResidueOrthogonal K n (A ⊓ B) =
      normResidueOrthogonal K n A ⊔ normResidueOrthogonal K n B := by
  rw [inf_comm, normResidueOrthogonal_inf_of_le_left hB, sup_comm]

/-! ### The norm group of a Kummer extension -/

/-- In any field extension `E/K` and for any subgroup `B ≤ Kˣ`, every element orthogonal to `B`
under the norm-residue symbol is a norm from the Kummer field `K(B^{1/n}) ⊆ E`. -/
theorem normResidueOrthogonal_le_normGroup_kummerField (E : Type*) [Field E] [Algebra K E]
    (B : Subgroup Kˣ) :
    normResidueOrthogonal K n B ≤ normGroup K (kummerField E n B) := by
  set M := kummerField E n B
  intro a ha
  let ι : M →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let j : M →ₐ[K] AlgebraicClosure K := (separableClosure K (AlgebraicClosure K)).val.comp ι
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (α := Gal(AlgebraicClosure K/K)) (artinMap K a)
  have hτ : ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv K σ) = 1 := by
    refine AlgEquiv.coe_toAlgHom_injective <|
      algHom_ext_of_eq_adjoin K kummerField_def fun x ⟨b, hb, hx⟩ ↦ ?_
    set y : M := ⟨x, mem_kummerField_of_pow_eq hb hx⟩
    rw [AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom, AlgEquiv.one_apply]
    refine (Function.Injective.eq_iff (f := j) j.injective).1 ?_
    have hjy : j y ^ n = algebraMap K (AlgebraicClosure K) b := by
      have hy : y ^ n = algebraMap K M b := Subtype.ext (by simpa using hx)
      rw [← map_pow, hy, AlgHom.commutes]
    have hcomm : j (ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv K σ) y) = σ (j y) := by
      have hι : ((ι (ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv K σ) y) :
          SeparableClosure K) : AlgebraicClosure K) = σ (j y) := by
        rw [ι.restrictNormalHom_commutes, coe_absoluteGaloisGroupRestrictEquiv_apply]
        rfl
      exact hι
    rw [hcomm, normResidueSymbol_spec a b σ hσ hjy, ha b hb,
      Subgroup.coe_one, Units.val_one, map_one, one_mul]
  rw [← localArtinMap_eq_zero_iff K M ι, artinMap_restrict K M ι a σ hσ, hτ, map_one, ofMul_one]

/-- **The norm group of a Kummer extension, general root-existence form.** If every `b ∈ B` has an
`n`-th root in `E`, then the norm subgroup of `K(B^{1/n})/K` is the orthogonal subgroup `B^⊥`. -/
theorem normGroup_kummerField_eq_normResidueOrthogonal_of_forall_exists_pow_eq {E : Type*}
    [Field E] [Algebra K E] {B : Subgroup Kˣ}
    (hroots : ∀ b ∈ B, ∃ x : E, x ^ n = algebraMap K E b) :
    normGroup K (kummerField E n B) = normResidueOrthogonal K n B := by
  refine le_antisymm (fun a ha b hb ↦ ?_) (normResidueOrthogonal_le_normGroup_kummerField E B)
  set M := kummerField E n B
  obtain ⟨y, hy⟩ := exists_pow_eq_kummerField hroots b hb
  have : FiniteDimensional K K⟮y⟯ :=
    adjoin.finiteDimensional (.of_pow (NeZero.pos n) (hy ▸ isIntegral_algebraMap))
  have ht : AdjoinSimple.gen K y ^ n = algebraMap K K⟮y⟯ b := Subtype.ext (by simpa using hy)
  exact (normResidueSymbol_eq_one_iff_mem_normGroup a b ht (adjoin_adjoinSimple_gen_eq_top y)).2
    (K⟮y⟯.val.normGroup_le_normGroup ha)

/-- **The norm group of a Kummer extension.** Inside any separably closed extension `E` of `K`, the
norm subgroup of the Kummer extension `K(B^{1/n})/K` equals `normResidueOrthogonal K n B`. -/
theorem normGroup_kummerField_eq_normResidueOrthogonal (E : Type*) [Field E] [Algebra K E]
    [IsSepClosed E] (B : Subgroup Kˣ) :
    normGroup K (kummerField E n B) = normResidueOrthogonal K n B := by
  have : NeZero (n : K) := (HasEnoughRootsOfUnity.exists_isPrimitiveRoot K n).choose_spec.neZero'
  have : NeZero (n : E) := .nat_of_injective (algebraMap K E).injective
  exact normGroup_kummerField_eq_normResidueOrthogonal_of_forall_exists_pow_eq
    fun b _ ↦ IsSepClosed.exists_pow_nat_eq (algebraMap K E b) n

/-- **Kummer realization of norm subgroups (Fesenko–Vostokov, Theorem IV.5.2).** Inside any
separably closed extension `E` of `K` and for any subgroup `B ≤ Kˣ`, the Kummer field
`K((B^⊥)^{1/n})` has norm subgroup `B ⊔ (Kˣ)ⁿ`. -/
theorem normGroup_kummerField_normResidueOrthogonal (E : Type*) [Field E] [Algebra K E]
    [IsSepClosed E] (B : Subgroup Kˣ) :
    normGroup K (kummerField E n (normResidueOrthogonal K n B)) = B ⊔ powerSubgroup Kˣ n :=
  (normGroup_kummerField_eq_normResidueOrthogonal E (normResidueOrthogonal K n B)).trans
    (normResidueOrthogonal_normResidueOrthogonal B)

/-- **Kummer realization of a subgroup containing `(Kˣ)ⁿ` as a norm subgroup.** For any subgroup
`A ≤ Kˣ` with `(Kˣ)ⁿ ≤ A` and any separably closed extension `E` of `K`, the Kummer field
`K((A^⊥)^{1/n})` has norm subgroup `A`. -/
theorem normGroup_kummerField_normResidueOrthogonal_of_le (E : Type*) [Field E] [Algebra K E]
    [IsSepClosed E] {A : Subgroup Kˣ} (hA : powerSubgroup Kˣ n ≤ A) :
    normGroup K (kummerField E n (normResidueOrthogonal K n A)) = A :=
  (normGroup_kummerField_normResidueOrthogonal E A).trans (sup_eq_left.2 hA)

/-- The index of `B^⊥` in `Kˣ` equals the relative index `[B : B ∩ (Kˣ)ⁿ]`. -/
theorem index_normResidueOrthogonal (B : Subgroup Kˣ) :
    (normResidueOrthogonal K n B).index = (powMonoidHom n : Kˣ →* Kˣ).range.relIndex B := by
  have : NeZero (n : K) := (HasEnoughRootsOfUnity.exists_isPrimitiveRoot K n).choose_spec.neZero'
  have : NeZero (n : SeparableClosure K) := .nat_of_injective (algebraMap K _).injective
  rw [← normGroup_kummerField_eq_normResidueOrthogonal (SeparableClosure K) B,
    index_normGroup_of_isMulCommutative,
    finrank_kummerField fun b _ ↦ IsSepClosed.exists_pow_nat_eq _ n]

end TauCeti
