/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import TauCeti.Algebra.AddCircle
public import TauCeti.Topology.Algebra.Group.LocallyConstant

/-!
# The carry cocycle of a character

Let `G` be a topological group, `M` a topological `G`-module, `χ : G → ℚ/ℤ` a character with open
kernel and `a ∈ M^G` an invariant. Write `χ'(g) ∈ [0, 1)` for the representative of `χ(g)`. Then

```text
(g, h) ↦ (χ'(g) + χ'(h) - χ'(gh)) • a = ⌊χ'(g) + χ'(h)⌋ • a
```

is a continuous `2`-cocycle, the **carry cocycle** `characterCarryCocycle χ hχ a` of `χ` and `a`.
Classically, its class is the cup product `a ∪ δχ` of `a ∈ H⁰(G, M)` with the image `δχ` of
`χ ∈ H¹(G, ℚ/ℤ)` under the connecting map of `0 → ℤ → ℚ → ℚ/ℤ → 0`: the integer-valued cochain
`(g, h) ↦ χ'(g) + χ'(h) - χ'(gh)` is the coboundary of the rational lift `χ'` of `χ`. When `G` is
cyclic of order `n` and `χ` sends a generator `g` to `1 / n`, its value at `(gⁱ, gʲ)`, for
`i, j < n`, is `a` if `n ≤ i + j` and `0` otherwise (`characterCarry_eq_ite`): these are the
values of the carry cocycle of `a` at `g` that represents the two-periodicity class of `a`.

The class is additive in `a` by construction and additive in `χ`
(`characterCarryCocycle_add_character`), and the cocycle is natural along compatible pairs
(`cocyclesMap2_characterCarryCocycle`). Naturality is what computes the localizations of a global
carry class at the places of a number field, and additivity in `χ` reduces the local computation to
a character taking the value `1 / n` on a generator.

## Main definitions

* `TauCeti.ContCohomology.characterCarry χ g h`: the integer `⌊χ'(g) + χ'(h)⌋`.
* `TauCeti.ContCohomology.characterCarryCocycle χ hχ`: the carry cocycle of `χ`, additive in the
  invariant `a`.

## Main results

* `TauCeti.ContCohomology.intCast_characterCarry`: `⌊χ'(g) + χ'(h)⌋ = χ'(g) + χ'(h) - χ'(gh)`.
* `TauCeti.ContCohomology.characterCarry_eq_ite`: if `χ(g)` and `χ(h)` are the classes of
  `i / n` and `j / n` with `i, j < n`, the carry is `1` if `n ≤ i + j` and `0` otherwise.
* `TauCeti.ContCohomology.cocyclesMap2_characterCarryCocycle`: pulling back the carry cocycle of
  `χ` and `a` along a compatible pair `(φ, f)` gives the carry cocycle of `χ ∘ φ` and `f a`.
* `TauCeti.ContCohomology.characterCarryCocycle_add_character`,
  `TauCeti.ContCohomology.characterCarryCocycle_zsmul_character`: the class of the carry cocycle is
  additive in the character.

## References

* J.-P. Serre, *Local Fields*, Chapter XIV, §1.
* J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Chapter VII (Tate, *Global
  Class Field Theory*), §1.
-/

public section

noncomputable section

namespace TauCeti.ContCohomology

open groupCohomology

universe u v uH uN

section Carry

variable {G : Type u} [Group G]

/-- **The carry of a character** `χ : G → ℚ/ℤ` at `(g, h)`: the integer `⌊χ'(g) + χ'(h)⌋`, where
`χ'(x) ∈ [0, 1)` is the representative of `χ(x)`. It is `χ'(g) + χ'(h) - χ'(gh)`
(`intCast_characterCarry`). -/
def characterCarry (χ : Additive G →+ AddCircle (1 : ℚ)) (g h : G) : ℤ :=
  ⌊(AddCircle.equivIco 1 0 (χ (.ofMul g)) : ℚ) + AddCircle.equivIco 1 0 (χ (.ofMul h))⌋

/-- The carry of `χ` at `(g, h)` is the defect `χ'(g) + χ'(h) - χ'(gh)` of additivity of the
representatives in `[0, 1)`. -/
theorem intCast_characterCarry (χ : Additive G →+ AddCircle (1 : ℚ)) (g h : G) :
    (characterCarry χ g h : ℚ) =
      AddCircle.equivIco 1 0 (χ (.ofMul g)) + AddCircle.equivIco 1 0 (χ (.ofMul h)) -
        AddCircle.equivIco 1 0 (χ (.ofMul (g * h))) := by
  rw [characterCarry, AddCircle.intCast_floor_equivIco_add, ofMul_mul, map_add χ]

/-- **The carry on classes of fractions**: if `χ(g)` and `χ(h)` are the classes of `i / n` and
`j / n` with `i, j < n`, the carry of `χ` at `(g, h)` is `1` if `n ≤ i + j` and `0` otherwise. -/
theorem characterCarry_eq_ite (χ : Additive G →+ AddCircle (1 : ℚ)) {g h : G} {n i j : ℕ}
    (hi : i < n) (hj : j < n) (hg : χ (.ofMul g) = ((i / n : ℚ) : AddCircle (1 : ℚ)))
    (hh : χ (.ofMul h) = ((j / n : ℚ) : AddCircle (1 : ℚ))) :
    characterCarry χ g h = if n ≤ i + j then 1 else 0 := by
  have hn : (0 : ℚ) < n := by exact_mod_cast hi.trans_le' (Nat.zero_le i)
  have hmem {k : ℕ} (hk : k < n) : (k / n : ℚ) ∈ Set.Ico (0 : ℚ) (0 + 1) :=
    ⟨by positivity, by rw [zero_add, div_lt_one hn]; exact_mod_cast hk⟩
  rw [characterCarry, hg, hh, AddCircle.equivIco_coe_of_mem (hmem hi),
    AddCircle.equivIco_coe_of_mem (hmem hj), ← add_div, Int.floor_eq_iff]
  have hij : ((i + j : ℕ) : ℚ) < 2 * n := by exact_mod_cast (by omega : i + j < 2 * n)
  push_cast at hij
  split_ifs with h
  · have : (n : ℚ) ≤ i + j := by exact_mod_cast h
    push_cast
    constructor
    · rwa [le_div_iff₀ hn, one_mul]
    · rw [div_lt_iff₀ hn]; linarith
  · have : (i + j : ℚ) < n := by exact_mod_cast not_le.1 h
    push_cast
    exact ⟨by positivity, by rwa [zero_add, div_lt_one hn]⟩

/-- The zero character has no carries. -/
@[simp]
theorem characterCarry_zero (g h : G) :
    characterCarry (0 : Additive G →+ AddCircle (1 : ℚ)) g h = 0 := by
  have h0 := AddCircle.equivIco_coe_of_mem (p := (1 : ℚ)) (a := 0) (y := 0) ⟨le_rfl, by norm_num⟩
  rw [AddCircle.coe_zero] at h0
  simp [characterCarry, h0]

/-- The carry of a character composed with a homomorphism is the carry at the images. -/
@[simp]
theorem characterCarry_comp {H : Type*} [Group H] (χ : Additive G →+ AddCircle (1 : ℚ))
    (φ : H →* G) (h k : H) :
    characterCarry (χ.comp φ.toAdditive) h k = characterCarry χ (φ h) (φ k) := by
  simp [characterCarry]

end Carry

section Cocycle

variable {G : Type u} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M]

/-- The carry of a character with open kernel is locally constant on `G × G`. -/
private theorem isLocallyConstant_characterCarry {χ : Additive G →+ AddCircle (1 : ℚ)}
    (hχ : IsOpen (χ.ker : Set (Additive G))) :
    IsLocallyConstant fun p : G × G ↦ characterCarry χ p.1 p.2 :=
  ((isLocallyConstant_character hχ).comp_continuous continuous_fst).comp₂
    ((isLocallyConstant_character hχ).comp_continuous continuous_snd) fun x y ↦
      ⌊(AddCircle.equivIco 1 0 x : ℚ) + AddCircle.equivIco 1 0 y⌋

/-- The carry cochain of a character and an invariant is a continuous `2`-cocycle. -/
private theorem characterCarry_smul_mem_Z2 {χ : Additive G →+ AddCircle (1 : ℚ)}
    (hχ : IsOpen (χ.ker : Set (Additive G))) (a : H0 G M) :
    (fun p : G × G ↦ characterCarry χ p.1 p.2 • (a : M)) ∈ Z2 G M := by
  refine mem_Z2_iff.2
    ⟨((isLocallyConstant_characterCarry hχ).comp fun k : ℤ ↦ k • (a : M)).continuous,
      fun g h j ↦ ?_⟩
  have hfix : g • (a : M) = a := (FixedPoints.mem_addSubgroup G M a).1 a.2 g
  -- The integer identity behind the cocycle condition, checked in `ℚ` by telescoping.
  have hcarry : characterCarry χ (g * h) j + characterCarry χ g h =
      characterCarry χ h j + characterCarry χ g (h * j) := by
    have h₁ := intCast_characterCarry χ (g * h) j
    have h₂ := intCast_characterCarry χ g h
    have h₃ := intCast_characterCarry χ h j
    have h₄ := intCast_characterCarry χ g (h * j)
    rw [mul_assoc] at h₁
    exact_mod_cast (by linarith : (characterCarry χ (g * h) j + characterCarry χ g h : ℚ) =
      characterCarry χ h j + characterCarry χ g (h * j))
  simp only [smul_comm g _ (a : M), hfix, ← add_smul, hcarry]

/-- **The carry cocycle of a character** `χ : G → ℚ/ℤ` with open kernel and an invariant
`a ∈ M^G`: the continuous `2`-cocycle `(g, h) ↦ ⌊χ'(g) + χ'(h)⌋ • a`, where `χ'(x) ∈ [0, 1)`
represents `χ(x)` (`characterCarryCocycle_apply`). It is additive in `a`. -/
def characterCarryCocycle (χ : Additive G →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive G))) : H0 G M →+ Z2 G M where
  toFun a := ⟨_, characterCarry_smul_mem_Z2 hχ a⟩
  map_zero' := Subtype.ext (funext fun _ ↦ smul_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ ↦ smul_add _ _ _)

/-- The value of the carry cocycle of `χ` and `a` at `(g, h)` is the carry of `χ` times `a`. -/
@[simp]
theorem characterCarryCocycle_apply (χ : Additive G →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive G))) (a : H0 G M) (g h : G) :
    (characterCarryCocycle χ hχ a : G × G → M) (g, h) = characterCarry χ g h • (a : M) :=
  (rfl)

/-- **Naturality of the carry cocycle.** Pulling back the carry cocycle of `χ` and `a` along a
compatible pair `(φ, f)` gives the carry cocycle of `χ ∘ φ` and `f a`. -/
theorem cocyclesMap2_characterCarryCocycle {H : Type uH} [Group H] [TopologicalSpace H]
    [ContinuousMul H] {N : Type uN} [AddCommGroup N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [DistribMulAction H N] (φ : H →ₜ* G) (f : M →+ N)
    (hf : Continuous f) (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (χ : Additive G →+ AddCircle (1 : ℚ)) (hχ : IsOpen (χ.ker : Set (Additive G))) (a : H0 G M) :
    cocyclesMap2 G M H N φ f hf hequiv (characterCarryCocycle χ hχ a) =
      characterCarryCocycle (χ.comp (φ : H →* G).toAdditive)
        (by rw [← AddMonoidHom.comap_ker, AddSubgroup.coe_comap]
            exact hχ.preimage (continuous_ofMul.comp (φ.continuous.comp continuous_toMul)))
        (explicitMap0 G M φ f hequiv a) := by
  refine Subtype.ext (funext fun ⟨h, k⟩ ↦ ?_)
  simp [cocyclesMap2_apply, characterCarryCocycle_apply, map_zsmul]

/-- **Naturality of the carry class.** Pulling back the cohomology class of the carry cocycle of
`χ` and `a` along a compatible pair `(φ, f)` gives the carry class of `χ ∘ φ` and `f a`.

This is the degree-two cohomology form of `cocyclesMap2_characterCarryCocycle`. -/
theorem explicitMap2_characterCarryCocycle {H : Type uH} [Group H] [TopologicalSpace H]
    [ContinuousMul H] [ContinuousSMul G M]
    {N : Type uN} [AddCommGroup N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [DistribMulAction H N] [ContinuousSMul H N]
    (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (χ : Additive G →+ AddCircle (1 : ℚ)) (hχ : IsOpen (χ.ker : Set (Additive G)))
    (a : H0 G M) :
    explicitMap2 G M H N φ f hf hequiv (characterCarryCocycle χ hχ a : H2 G M) =
      (characterCarryCocycle (χ.comp (φ : H →* G).toAdditive)
        (by rw [← AddMonoidHom.comap_ker, AddSubgroup.coe_comap]
            exact hχ.preimage (continuous_ofMul.comp (φ.continuous.comp continuous_toMul)))
        (explicitMap0 G M φ f hequiv a) : H2 H N) := by
  rw [explicitMap2_mk, cocyclesMap2_characterCarryCocycle]

/-- **The class of the carry cocycle is additive in the character.** The carry cocycles of
`χ₁ + χ₂`, `χ₁` and `χ₂` differ by the coboundary of `g ↦ ⌊χ₁'(g) + χ₂'(g)⌋ • a`. The classes are
read in `Z² / B²`, which is `H2 G M` whenever the latter is defined. -/
theorem characterCarryCocycle_add_character
    {χ₁ χ₂ : Additive G →+ AddCircle (1 : ℚ)}
    (hχ₁ : IsOpen (χ₁.ker : Set (Additive G))) (hχ₂ : IsOpen (χ₂.ker : Set (Additive G)))
    (a : H0 G M) :
    (characterCarryCocycle (χ₁ + χ₂) (AddSubgroup.isOpen_mono (H₁ := χ₁.ker ⊓ χ₂.ker)
      (fun _ hx ↦ by simp_all [AddSubgroup.mem_inf]) (hχ₁.inter hχ₂)) a :
        Z2 G M ⧸ (B2 G M).addSubgroupOf (Z2 G M)) =
      characterCarryCocycle χ₁ hχ₁ a + characterCarryCocycle χ₂ hχ₂ a := by
  rw [← QuotientAddGroup.mk_add, H2pi_eq_iff]
  -- The primitive is `g ↦ -e(g) • a`, with `e(g) = ⌊χ₁'(g) + χ₂'(g)⌋`.
  let e : G → ℤ := fun g ↦
    ⌊(AddCircle.equivIco 1 0 (χ₁ (.ofMul g)) : ℚ) + AddCircle.equivIco 1 0 (χ₂ (.ofMul g))⌋
  have he (g : G) : (e g : ℚ) = AddCircle.equivIco 1 0 (χ₁ (.ofMul g)) +
      AddCircle.equivIco 1 0 (χ₂ (.ofMul g)) -
        AddCircle.equivIco 1 0 ((χ₁ + χ₂) (.ofMul g)) :=
    AddCircle.intCast_floor_equivIco_add _ _
  have hfix (g : G) : g • (a : M) = a := (FixedPoints.mem_addSubgroup G M a).1 a.2 g
  refine mem_B2_iff.2 ⟨fun g ↦ (-e g) • (a : M),
    (((isLocallyConstant_character hχ₁).comp₂ (isLocallyConstant_character hχ₂) fun x y ↦
      (-⌊(AddCircle.equivIco 1 0 x : ℚ) + AddCircle.equivIco 1 0 y⌋) • (a : M))).continuous,
    funext fun p ↦ ?_⟩
  obtain ⟨g, h⟩ := p
  -- The integer identity behind the coboundary, checked in `ℚ`.
  have key : -e h - -e (g * h) + -e g = characterCarry (χ₁ + χ₂) g h -
      (characterCarry χ₁ g h + characterCarry χ₂ g h) := by
    have h₁ := intCast_characterCarry (χ₁ + χ₂) g h
    have h₂ := intCast_characterCarry χ₁ g h
    have h₃ := intCast_characterCarry χ₂ g h
    have h₄ := he g
    have h₅ := he h
    have h₆ := he (g * h)
    exact_mod_cast (by linarith : (-e h - -e (g * h) + -e g : ℚ) = characterCarry (χ₁ + χ₂) g h -
      (characterCarry χ₁ g h + characterCarry χ₂ g h))
  simp only [d1_apply, hfix, smul_comm g _ (a : M), AddSubgroup.coe_add, Pi.sub_apply,
    Pi.add_apply, characterCarryCocycle_apply, ← sub_smul, ← add_smul, ← add_smul, key]

/-- The carry cocycle of the zero character vanishes. -/
@[simp]
theorem characterCarryCocycle_zero_character (a : H0 G M) :
    characterCarryCocycle 0 (by simp) a = 0 :=
  Subtype.ext (funext fun ⟨_, _⟩ ↦ by simp)

/-- **The class of the carry cocycle is additive in the character**: integer multiples. -/
theorem characterCarryCocycle_zsmul_character
    {χ : Additive G →+ AddCircle (1 : ℚ)} (hχ : IsOpen (χ.ker : Set (Additive G))) (k : ℤ)
    (a : H0 G M) :
    (characterCarryCocycle (k • χ) (AddSubgroup.isOpen_mono (fun _ hx ↦ by simp_all) hχ) a :
        Z2 G M ⧸ (B2 G M).addSubgroupOf (Z2 G M)) =
      k • (characterCarryCocycle χ hχ a : Z2 G M ⧸ (B2 G M).addSubgroupOf (Z2 G M)) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have h := characterCarryCocycle_add_character (isOpen_ker_zsmul hχ i) hχ a
    simp only [add_zsmul, one_zsmul]
    rw [h, ih]
  | pred i ih =>
    have h := characterCarryCocycle_add_character (isOpen_ker_zsmul hχ (-i - 1)) hχ a
    simp only [sub_zsmul, one_zsmul, neg_add_cancel_right] at h ⊢
    rw [eq_add_neg_iff_add_eq, ← h, ih]

end Cocycle

end TauCeti.ContCohomology
