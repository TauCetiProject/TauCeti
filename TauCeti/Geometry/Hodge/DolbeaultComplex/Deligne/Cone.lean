/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import TauCeti.Geometry.Hodge.DolbeaultComplex.Deligne.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The Deligne cone of a real Dolbeault complex

For a real Dolbeault complex `A` and an integer `p`, the Deligne cone is the homotopy fibre
`fib(A_ℝ(p) ⊕ FᵖA → A)` of the map `(r, f) ↦ f - r`, where `A_ℝ(p) = (2πi)ᵖ A_ℝ` is the twisted
real structure and `FᵖA` is the sum of the types `(r, s)` with `p ≤ r`. Its term in degree `n` is

`Kⁿ = (Aⁿ ∩ A_ℝ(p)) × (Aⁿ ∩ FᵖA) × Aⁿ⁻¹`,

with `Aⁿ` the sum of the types of total degree `n`, and its differential is
`(r, f, ω) ↦ (d r, d f, f - r - d ω)`. This is the pair fibre `d(a, b) = (d a, φ(a) - d b)` of the
map `φ(r, f) = f - r`.

Burgos showed that the small Deligne complex `D(A, p)`
(`TauCeti.Hodge.DolbeaultComplex.deligneComplex`) is a deformation retract of this cone. This file
constructs the comparison maps and the contraction explicitly. Write `π_q` for the projection
`TauCeti.Hodge.Conjugation.twistProj` to `A_ℝ(q)`, `π_L`, `π_Q`, `π_Qbar`, `π_PP` and `π_F` for the
projections onto the types `(r, s)` with `r, s < p`, with `r < p ≤ s`, with `s < p ≤ r`, with
`p ≤ r, s`, and with `p ≤ r`. Then:

* the inclusion `D(A, p) → K` sends `x` to `(π_Qbar d x - π_Q d x, 2 π_Qbar d x, x)` in degrees
  `n < 2p` and to `(x, x, 0)` from degree `2p` on. In degrees `n < 2p` the vector `x` has the types
  `(r, s)` with `r, s < p` and `r + s = n - 1`, so `π_Qbar d x = ∂ x^{p-1, n-p}` and
  `π_Q d x = ∂bar x^{n-p, p-1}`;
* the projection `K → D(A, p)` sends `(r, f, ω)` to `π_{p-1} π_L ω` in degrees `n < 2p` and to
  `π_PP r + 2 π_p π_PP d π_Q ω` from degree `2p` on. In degrees `n ≥ 2p` the vector
  `π_PP d π_Q ω` is `∂ ω^{p-1, n-p}`;
* the contraction `K → K` of degree `-1` sends `(r, f, ω)` to
  `(π_p (π_L ω + 2 π_Q ω), 2 π_p π_Q ω - π_Q ω - π_F ω, 0)`, in every degree.

The projection after the inclusion is the identity of `D(A, p)`, and the inclusion after the
projection is homotopic to the identity of the cone through the contraction. So the two complexes
are homotopy equivalent. For the logarithmic Dolbeault algebra of a smooth complex variety the cone
computes real Deligne–Beilinson cohomology, and this equivalence is how the small complex
`D(A, p)` computes it too.

As for the Deligne complex, the terms of the cone are real subspaces of a single ambient space,
here `A × A × A`, and the differential, the comparison maps and the contraction are restrictions
of linear maps between the ambient spaces.

## Main definitions

* `TauCeti.Hodge.DolbeaultComplex.deligneConePiece`: the term `Kⁿ` of the cone.
* `TauCeti.Hodge.DolbeaultComplex.deligneConeDiff`: the differential of the cone.
* `TauCeti.Hodge.DolbeaultComplex.deligneCone`: the Deligne cone, a real cochain complex.
* `TauCeti.Hodge.DolbeaultComplex.deligneToCone`: the inclusion `D(A, p) ⟶ K`.
* `TauCeti.Hodge.DolbeaultComplex.coneToDeligne`: the projection `K ⟶ D(A, p)`.
* `TauCeti.Hodge.DolbeaultComplex.deligneConeContraction`: the contraction of degree `-1`.
* `TauCeti.Hodge.DolbeaultComplex.deligneConeHomotopy`: the homotopy from the inclusion after the
  projection to the identity of the cone.
* `TauCeti.Hodge.DolbeaultComplex.deligneHomotopyEquivCone`: the homotopy equivalence between the
  Deligne complex and the Deligne cone.

## Main results

* `TauCeti.Hodge.DolbeaultComplex.deligneToCone_comp_coneToDeligne`: the projection after the
  inclusion is the identity.
* `TauCeti.Hodge.DolbeaultComplex.deligneToConeMap_coneToDeligneMap`: on the cone, the inclusion
  after the projection is `h d + d h + 1`, with `h` the contraction.

## References

* J. I. Burgos Gil, *Arithmetic Chow rings and Deligne–Beilinson cohomology*, J. Algebraic Geom.
  6 (1997), 335–377.
* J. I. Burgos Gil, J. Kramer, U. Kühn, *Cohomological arithmetic Chow rings*, J. Inst. Math.
  Jussieu 6 (2007), Definitions 5.7–5.10 and Proposition 5.12.
-/

public section

open CategoryTheory TauCeti.DirectSum

namespace TauCeti.Hodge

universe u

namespace DolbeaultComplex

variable {A : Type u} [AddCommGroup A] [Module ℂ A] {𝒜 : ℤ × ℤ → Submodule ℂ A}
  (X : DolbeaultComplex 𝒜)

/-- Decide membership of types `(r, s)` in regions cut out by linear inequalities, after unfolding
the membership in the regions and their unions. -/
local macro "region_omega" : tactic =>
  `(tactic| (intros; simp only [Set.mem_union, Set.mem_ofPred_eq, Prod.fst_swap,
    Prod.snd_swap] at *; omega))

/-- The term `Kⁿ = (Aⁿ ∩ A_ℝ(p)) × (Aⁿ ∩ FᵖA) × Aⁿ⁻¹` of the Deligne cone, where `Aⁿ` is the sum
of the types `(r, s)` with `r + s = n` and `FᵖA` the sum of those with `p ≤ r`. -/
def deligneConePiece (p n : ℤ) : Submodule ℝ (A × A × A) :=
  ((⨆ i : {i : ℤ × ℤ | i.1 + i.2 = n}, 𝒜 i).restrictScalars ℝ ⊓ X.conj.twist p).prod
    (((⨆ i : {i : ℤ × ℤ | i.1 + i.2 = n ∧ p ≤ i.1}, 𝒜 i).restrictScalars ℝ).prod
      ((⨆ i : {i : ℤ × ℤ | i.1 + i.2 = n - 1}, 𝒜 i).restrictScalars ℝ))

variable {X} in
/-- Membership in a term of the Deligne cone, componentwise. -/
theorem mem_deligneConePiece {p n : ℤ} {x : A × A × A} :
    x ∈ X.deligneConePiece p n ↔
      (x.1 ∈ (⨆ i : {i : ℤ × ℤ | i.1 + i.2 = n}, 𝒜 i) ∧ x.1 ∈ X.conj.twist p) ∧
        x.2.1 ∈ (⨆ i : {i : ℤ × ℤ | i.1 + i.2 = n ∧ p ≤ i.1}, 𝒜 i) ∧
        x.2.2 ∈ (⨆ i : {i : ℤ × ℤ | i.1 + i.2 = n - 1}, 𝒜 i) :=
  Iff.rfl

/-- The differential `(r, f, ω) ↦ (d r, d f, f - r - d ω)` of the Deligne cone, on the ambient
space `A × A × A`. -/
def deligneConeDiff : A × A × A →ₗ[ℂ] A × A × A where
  toFun x := (X.d x.1, X.d x.2.1, x.2.1 - x.1 - X.d x.2.2)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk, Prod.mk.injEq, true_and]
    abel
  map_smul' c x := by simp [smul_sub]

/-- The differential of the Deligne cone is `(r, f, ω) ↦ (d r, d f, f - r - d ω)`. -/
@[simp]
theorem deligneConeDiff_apply (x : A × A × A) :
    X.deligneConeDiff x = (X.d x.1, X.d x.2.1, x.2.1 - x.1 - X.d x.2.2) :=
  (rfl)

/-- The differential of the Deligne cone squares to zero, on the whole ambient space. -/
theorem deligneConeDiff_deligneConeDiff (x : A × A × A) :
    X.deligneConeDiff (X.deligneConeDiff x) = 0 := by
  simp [map_sub]

variable {X}

/-- The differential of the Deligne cone carries `Kⁿ` into `Kⁿ⁺¹`. -/
theorem deligneConeDiff_mem {p n : ℤ} {x : A × A × A} (hx : x ∈ X.deligneConePiece p n) :
    X.deligneConeDiff x ∈ X.deligneConePiece p (n + 1) := by
  obtain ⟨⟨hr, hr'⟩, hf, hω⟩ := mem_deligneConePiece.1 hx
  have hn : {i : ℤ × ℤ | i.1 + i.2 = n ∧ p ≤ i.1} ⊆ {i | i.1 + i.2 = n} := fun _ hi ↦ hi.1
  have hf' : x.2.1 ∈ ⨆ i : {i : ℤ × ℤ | i.1 + i.2 = n}, 𝒜 i := mem_iSup_of_subset hn hf
  refine mem_deligneConePiece.2 ⟨⟨X.d_mem_iSup_degree rfl hr,
    X.conj.map_mem_twist X.conj (conj_d X) hr'⟩, X.d_mem_iSup (by region_omega) hf, ?_⟩
  · rw [add_sub_cancel_right]
    exact sub_mem (sub_mem hf' hr) (X.d_mem_iSup_degree (sub_add_cancel n 1) hω)

variable (X)

/-- The Deligne cone `fib(A_ℝ(p) ⊕ FᵖA → A)` of a real Dolbeault complex: the real cochain
complex whose term in degree `n` is `TauCeti.Hodge.DolbeaultComplex.deligneConePiece` and whose
differential is the restriction of `TauCeti.Hodge.DolbeaultComplex.deligneConeDiff`.

The body is exposed so that, as for `TauCeti.Hodge.DolbeaultComplex.deligneComplex`, the terms of
the complex are the real subspaces `TauCeti.Hodge.DolbeaultComplex.deligneConePiece` of
`A × A × A`. -/
@[expose]
noncomputable def deligneCone (p : ℤ) : CochainComplex (ModuleCat.{u} ℝ) ℤ :=
  CochainComplex.of (fun n ↦ ModuleCat.of ℝ (X.deligneConePiece p n))
    (fun n ↦ ModuleCat.ofHom (LinearMap.restrict (p := X.deligneConePiece p n)
      (q := X.deligneConePiece p (n + 1)) (X.deligneConeDiff.restrictScalars ℝ)
      fun _ hx ↦ deligneConeDiff_mem hx))
    fun _ ↦ ModuleCat.hom_ext
      (LinearMap.ext fun x ↦ Subtype.ext (X.deligneConeDiff_deligneConeDiff x.val))

/-- The term of the Deligne cone in degree `n` is `Kⁿ`. -/
@[simp]
theorem deligneCone_X (p n : ℤ) :
    (X.deligneCone p).X n = ModuleCat.of ℝ (X.deligneConePiece p n) :=
  (rfl)

/-- The differential of the Deligne cone between degrees `n` and `m = n + 1` is the restriction of
`TauCeti.Hodge.DolbeaultComplex.deligneConeDiff`. -/
@[simp]
theorem deligneCone_d_apply (p : ℤ) {n m : ℤ} (h : n + 1 = m) (x : X.deligneConePiece p n) :
    Subtype.val (p := (· ∈ X.deligneConePiece p m)) ((X.deligneCone p).d n m x) =
      X.deligneConeDiff x := by
  subst h
  simp only [deligneCone, CochainComplex.of_d, ModuleCat.hom_ofHom]
  -- The terms of `CochainComplex.of` are only definitionally the subtypes `deligneConePiece`, so
  -- `LinearMap.coe_restrict_apply` cannot be rewritten here and is applied up to that unfolding.
  exact LinearMap.coe_restrict_apply _ x

section Decomposition

variable [DirectSum.Decomposition 𝒜]

/-! ### The comparison maps on the ambient spaces -/

/-- The complex-linear map `A → A × A × A` whose restriction to `Dⁿ(A, p)` is the inclusion of
the Deligne complex into the Deligne cone: `x ↦ (π_Qbar d x - π_Q d x, 2 π_Qbar d x, x)` for
`n < 2p`, where `π_Qbar` and `π_Q` project onto the types `(r, s)` with `s < p ≤ r` and with
`r < p ≤ s`, and `x ↦ (x, x, 0)` for `2p ≤ n`. -/
noncomputable def deligneToConeMap (p n : ℤ) : A →ₗ[ℂ] A × A × A :=
  if n < 2 * p then
    ((supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p} - supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2}) ∘ₗ
      X.d).prod ((2 • (supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p} ∘ₗ X.d)).prod LinearMap.id)
  else LinearMap.id.prod (LinearMap.id.prod 0)

variable {X}

/-- Below the critical degree the inclusion into the Deligne cone is
`x ↦ (π_Qbar d x - π_Q d x, 2 π_Qbar d x, x)`. -/
theorem deligneToConeMap_of_lt {p n : ℤ} (h : n < 2 * p) (x : A) :
    X.deligneToConeMap p n x =
      (supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p} (X.d x) -
          supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} (X.d x),
        2 • supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p} (X.d x), x) := by
  rw [deligneToConeMap, ite_eq_left h]
  rfl

/-- From the critical degree on the inclusion into the Deligne cone is `x ↦ (x, x, 0)`. -/
theorem deligneToConeMap_of_le {p n : ℤ} (h : 2 * p ≤ n) (x : A) :
    X.deligneToConeMap p n x = (x, x, 0) := by
  rw [deligneToConeMap, ite_eq_right (not_lt.2 h)]
  rfl

variable (X)

/-- The real-linear map `A × A × A → A` whose restriction to `Kⁿ` is the projection of the Deligne
cone onto the Deligne complex: `(r, f, ω) ↦ π_{p-1} π_L ω` for `n < 2p`, where `π_L` projects onto
the types `(r, s)` with `r, s < p`, and `(r, f, ω) ↦ π_PP r + 2 π_p π_PP d π_Q ω` for `2p ≤ n`,
where `π_PP` and `π_Q` project onto the types with `p ≤ r, s` and with `r < p ≤ s`. -/
noncomputable def coneToDeligneMap (p n : ℤ) : A × A × A →ₗ[ℝ] A :=
  if n < 2 * p then
    X.conj.twistProj (p - 1) ∘ₗ (supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p}).restrictScalars ℝ ∘ₗ
      LinearMap.snd ℝ A A ∘ₗ LinearMap.snd ℝ A (A × A)
  else
    (supportedProj 𝒜 {i | p ≤ i.1 ∧ p ≤ i.2}).restrictScalars ℝ ∘ₗ LinearMap.fst ℝ A (A × A) +
      2 • (X.conj.twistProj p ∘ₗ (supportedProj 𝒜 {i | p ≤ i.1 ∧ p ≤ i.2} ∘ₗ X.d ∘ₗ
        supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2}).restrictScalars ℝ ∘ₗ
          LinearMap.snd ℝ A A ∘ₗ LinearMap.snd ℝ A (A × A))

variable {X}

/-- Below the critical degree the projection onto the Deligne complex is
`(r, f, ω) ↦ π_{p-1} π_L ω`. -/
theorem coneToDeligneMap_of_lt {p n : ℤ} (h : n < 2 * p) (x : A × A × A) :
    X.coneToDeligneMap p n x =
      X.conj.twistProj (p - 1) (supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} x.2.2) := by
  rw [coneToDeligneMap, ite_eq_left h]
  rfl

/-- From the critical degree on the projection onto the Deligne complex is
`(r, f, ω) ↦ π_PP r + 2 π_p π_PP d π_Q ω`. -/
theorem coneToDeligneMap_of_le {p n : ℤ} (h : 2 * p ≤ n) (x : A × A × A) :
    X.coneToDeligneMap p n x =
      supportedProj 𝒜 {i | p ≤ i.1 ∧ p ≤ i.2} x.1 + 2 • X.conj.twistProj p
        (supportedProj 𝒜 {i | p ≤ i.1 ∧ p ≤ i.2}
          (X.d (supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} x.2.2))) := by
  rw [coneToDeligneMap, ite_eq_right (not_lt.2 h)]
  rfl

variable (X)

/-- The first component `ω ↦ π_p (π_L ω + 2 π_Q ω)` of the contraction of the Deligne cone. -/
private noncomputable def contractionFst (p : ℤ) : A →ₗ[ℝ] A :=
  X.conj.twistProj p ∘ₗ (supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} +
    2 • supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2}).restrictScalars ℝ

/-- The second component `ω ↦ 2 π_p π_Q ω - π_Q ω - π_F ω` of the contraction of the Deligne
cone. -/
private noncomputable def contractionSnd (p : ℤ) : A →ₗ[ℝ] A :=
  2 • (X.conj.twistProj p ∘ₗ (supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2}).restrictScalars ℝ) -
    (supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} + supportedProj 𝒜 {i | p ≤ i.1}).restrictScalars ℝ

private theorem contractionFst_apply (p : ℤ) (ω : A) :
    contractionFst X p ω = X.conj.twistProj p (supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} ω) +
      2 • X.conj.twistProj p (supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} ω) := by
  simp [contractionFst]

private theorem contractionSnd_apply (p : ℤ) (ω : A) :
    contractionSnd X p ω = 2 • X.conj.twistProj p (supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} ω) -
      supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} ω - supportedProj 𝒜 {i | p ≤ i.1} ω := by
  simp [contractionSnd, sub_add_eq_sub_sub]

/-- The contraction of degree `-1` of the Deligne cone, on the ambient space `A × A × A`:
`(r, f, ω) ↦ (π_p (π_L ω + 2 π_Q ω), 2 π_p π_Q ω - π_Q ω - π_F ω, 0)`, where `π_L`, `π_Q` and
`π_F` project onto the types `(r, s)` with `r, s < p`, with `r < p ≤ s` and with `p ≤ r`. -/
noncomputable def deligneConeContraction (p : ℤ) : A × A × A →ₗ[ℝ] A × A × A :=
  (contractionFst X p ∘ₗ LinearMap.snd ℝ A A ∘ₗ LinearMap.snd ℝ A (A × A)).prod
    ((contractionSnd X p ∘ₗ LinearMap.snd ℝ A A ∘ₗ LinearMap.snd ℝ A (A × A)).prod 0)

private theorem deligneConeContraction_eq (p : ℤ) (x : A × A × A) :
    X.deligneConeContraction p x = (contractionFst X p x.2.2, contractionSnd X p x.2.2, 0) :=
  (rfl)

/-- The contraction of the Deligne cone is
`(r, f, ω) ↦ (π_p (π_L ω + 2 π_Q ω), 2 π_p π_Q ω - π_Q ω - π_F ω, 0)`. -/
theorem deligneConeContraction_apply (p : ℤ) (x : A × A × A) :
    X.deligneConeContraction p x =
      (X.conj.twistProj p (supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} x.2.2 +
          2 • supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} x.2.2),
        2 • X.conj.twistProj p (supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} x.2.2) -
          supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} x.2.2 - supportedProj 𝒜 {i | p ≤ i.1} x.2.2,
        0) := by
  rw [deligneConeContraction_eq, contractionFst_apply, contractionSnd_apply, map_add, map_nsmul]

/-! ### Projections onto the four regions of types

The types `(r, s)` split into the regions `r, s < p`, `r < p ≤ s`, `s < p ≤ r` and `p ≤ r, s`.
The lemmas below record how the projections onto these regions interact with `d` and the
conjugation. -/

variable {X}

variable (𝒜) in
/-- The projections onto the four regions of types add up to the identity. -/
private theorem supportedProj_partition (p : ℤ) (y : A) :
    supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} y + supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} y +
        supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p} y + supportedProj 𝒜 {i | p ≤ i.1 ∧ p ≤ i.2} y =
      y := by
  have hU : (Set.univ : Set (ℤ × ℤ)) = {i | i.1 < p ∧ i.2 < p} ∪ {i | i.1 < p ∧ p ≤ i.2} ∪
      {i | p ≤ i.1 ∧ i.2 < p} ∪ {i | p ≤ i.1 ∧ p ≤ i.2} := by
    ext i
    simp only [Set.mem_univ, Set.mem_union, Set.mem_ofPred_eq, true_iff]
    omega
  conv_rhs => rw [← supportedProj_univ 𝒜 y, hU]
  rw [supportedProj_union, supportedProj_union, supportedProj_union] <;>
    exact Set.disjoint_left.2 (by region_omega)

variable (𝒜) in
/-- The projection onto the types `(r, s)` with `p ≤ r` is the sum of the projections onto the
types with `s < p ≤ r` and with `p ≤ r, s`. -/
private theorem supportedProj_hodge (p : ℤ) (y : A) :
    supportedProj 𝒜 {i | p ≤ i.1} y =
      supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p} y + supportedProj 𝒜 {i | p ≤ i.1 ∧ p ≤ i.2} y := by
  have hU : {i : ℤ × ℤ | p ≤ i.1} = {i | p ≤ i.1 ∧ i.2 < p} ∪ {i | p ≤ i.1 ∧ p ≤ i.2} := by
    ext i
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    omega
  rw [hU, supportedProj_union]
  exact Set.disjoint_left.2 (by region_omega)

variable (X) in
/-- `π_S d π_T = 0` when `d` carries no type in `T` into `S`. -/
private theorem supportedProj_d_supportedProj_eq_zero {S T : Set (ℤ × ℤ)}
    (h : ∀ i ∈ T, (i.1 + 1, i.2) ∉ S ∧ (i.1, i.2 + 1) ∉ S) (y : A) :
    supportedProj 𝒜 S (X.d (supportedProj 𝒜 T y)) = 0 :=
  supportedProj_eq_zero_of_disjoint disjoint_compl_right
    (X.d_mem_iSup (T := Sᶜ) h (supportedProj_mem_iSup 𝒜 T y))

/-- Conjugation carries the projection onto the types `(r, s)` with `r < p ≤ s` to the projection
onto the types with `s < p ≤ r`. -/
private theorem conj_supportedProj_mixed (p : ℤ) (y : A) :
    X.conj.toEquiv (supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} y) =
      supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p} (X.conj.toEquiv y) :=
  X.conj_supportedProj (fun i ↦ by simp only [Set.mem_ofPred_eq, Prod.fst_swap, Prod.snd_swap,
    and_comm]) y

/-- Conjugation commutes with the projection onto a set of types stable under exchange. -/
private theorem conj_supportedProj_low (p : ℤ) (y : A) :
    X.conj.toEquiv (supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} y) =
      supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} (X.conj.toEquiv y) :=
  X.conj_supportedProj (fun i ↦ by simp only [Set.mem_ofPred_eq, Prod.fst_swap, Prod.snd_swap,
    and_comm]) y

/-- Conjugation commutes with the projection onto a set of types stable under exchange. -/
private theorem conj_supportedProj_high (p : ℤ) (y : A) :
    X.conj.toEquiv (supportedProj 𝒜 {i | p ≤ i.1 ∧ p ≤ i.2} y) =
      supportedProj 𝒜 {i | p ≤ i.1 ∧ p ≤ i.2} (X.conj.toEquiv y) :=
  X.conj_supportedProj (fun i ↦ by simp only [Set.mem_ofPred_eq, Prod.fst_swap, Prod.snd_swap,
    and_comm]) y

/-- Conjugation carries the projection onto the types `(r, s)` with `s < p ≤ r` to the projection
onto the types with `r < p ≤ s`. -/
private theorem conj_supportedProj_mixedBar (p : ℤ) (y : A) :
    X.conj.toEquiv (supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p} y) =
      supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} (X.conj.toEquiv y) :=
  X.conj_supportedProj (fun i ↦ by simp only [Set.mem_ofPred_eq, Prod.fst_swap, Prod.snd_swap,
    and_comm]) y

/-- The projection onto the types `(r, s)` with `r < p ≤ s` after `d`. -/
private theorem supportedProj_mixed_d (p : ℤ) (y : A) :
    supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} (X.d y) =
      supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} (X.d (supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} y)) +
        X.d (supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} y) -
        supportedProj 𝒜 {i | p ≤ i.1 ∧ p ≤ i.2}
          (X.d (supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} y)) := by
  have hq := supportedProj_partition 𝒜 p (X.d (supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} y))
  conv_lhs => rw [← supportedProj_partition 𝒜 p y]
  simp (disch := region_omega) only [map_add,
    supportedProj_d_supportedProj_eq_zero, add_zero, zero_add] at hq ⊢
  rw [← eq_sub_iff_add_eq] at hq
  rw [hq, add_sub_assoc]

/-- The projection onto the types `(r, s)` with `s < p ≤ r` after `d`, the conjugate of the
identity for the types with `r < p ≤ s`. -/
private theorem supportedProj_mixedBar_d (p : ℤ) (y : A) :
    supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p} (X.d y) =
      supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p} (X.d (supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} y)) +
        X.d (supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p} y) -
        supportedProj 𝒜 {i | p ≤ i.1 ∧ p ≤ i.2}
          (X.d (supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p} y)) := by
  -- Conjugate the identity for the types `r < p ≤ s` at the conjugate of `y`.
  simpa only [map_add, map_sub, conj_supportedProj_mixed, conj_supportedProj_low,
    conj_supportedProj_high, conj_d, Conjugation.apply_apply] using
    congrArg X.conj.toEquiv (supportedProj_mixed_d (X := X) p (X.conj.toEquiv y))

/-- The projection onto the types `(r, s)` with `r, s < p` after `d`. -/
private theorem supportedProj_low_d (p : ℤ) (y : A) :
    supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} (X.d y) =
      X.d (supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} y) -
        supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} (X.d (supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} y)) -
        supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p}
          (X.d (supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} y)) := by
  have ha := supportedProj_partition 𝒜 p (X.d (supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} y))
  conv_lhs => rw [← supportedProj_partition 𝒜 p y]
  simp (disch := region_omega) only [map_add,
    supportedProj_d_supportedProj_eq_zero, add_zero] at ha ⊢
  rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq, add_right_comm, ha]

/-- The projection onto the types `(r, s)` with `p ≤ r` after `d`. -/
private theorem supportedProj_hodge_d (p : ℤ) (y : A) :
    supportedProj 𝒜 {i | p ≤ i.1} (X.d y) =
      supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p} (X.d (supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} y)) +
        supportedProj 𝒜 {i | p ≤ i.1 ∧ p ≤ i.2} (X.d (supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} y)) +
        X.d (supportedProj 𝒜 {i | p ≤ i.1} y) := by
  have ht := supportedProj_partition 𝒜 p (X.d (supportedProj 𝒜 {i | p ≤ i.1 ∧ p ≤ i.2} y))
  have hy : supportedProj 𝒜 {i | p ≤ i.1 ∧ p ≤ i.2} (X.d y) =
      supportedProj 𝒜 {i | p ≤ i.1 ∧ p ≤ i.2} (X.d (supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} y)) +
        supportedProj 𝒜 {i | p ≤ i.1 ∧ p ≤ i.2} (X.d (supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p} y)) +
        X.d (supportedProj 𝒜 {i | p ≤ i.1 ∧ p ≤ i.2} y) := by
    conv_lhs => rw [← supportedProj_partition 𝒜 p y]
    simp (disch := region_omega) only [map_add,
      supportedProj_d_supportedProj_eq_zero, add_zero, zero_add] at ht ⊢
    rw [ht]
  rw [supportedProj_hodge 𝒜 p (X.d y), supportedProj_hodge 𝒜 p y, supportedProj_mixedBar_d, hy,
    map_add]
  abel

/-- A sum of type pieces of total degree `m < 2p` has no part of type `(r, s)` with `p ≤ r, s`. -/
private theorem supportedProj_high_eq_zero {p m : ℤ} (hm : m < 2 * p) {y : A}
    (hy : y ∈ ⨆ i : {i : ℤ × ℤ | i.1 + i.2 = m}, 𝒜 i) :
    supportedProj 𝒜 {i | p ≤ i.1 ∧ p ≤ i.2} y = 0 :=
  supportedProj_eq_zero_of_disjoint (Set.disjoint_left.2 (by region_omega)) hy

/-- A sum of type pieces of total degree `m ≥ 2p - 1` has no part of type `(r, s)` with
`r, s < p`. -/
private theorem supportedProj_low_eq_zero {p m : ℤ} (hm : 2 * p - 1 ≤ m) {y : A}
    (hy : y ∈ ⨆ i : {i : ℤ × ℤ | i.1 + i.2 = m}, 𝒜 i) :
    supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} y = 0 :=
  supportedProj_eq_zero_of_disjoint (Set.disjoint_left.2 (by region_omega)) hy

/-! ### The contraction -/

/-- The third component of `h d + d h + 1`: with `h` the contraction, it is `π_{p-1} π_L ω`. -/
private theorem contractionSnd_sub_contractionFst_add (p : ℤ) (ω : A) :
    contractionSnd X p ω - contractionFst X p ω + ω =
      X.conj.twistProj (p - 1) (supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} ω) := by
  rw [contractionSnd_apply, contractionFst_apply, supportedProj_hodge 𝒜 p ω]
  linear_combination (norm := abel) -supportedProj_partition 𝒜 p ω -
    X.conj.twistProj_add_twistProj_sub_one p (supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} ω)

/-- The commutator of `d` with the first component of the contraction. -/
private theorem d_contractionFst_sub (p : ℤ) (ω : A) :
    X.d (contractionFst X p ω) - contractionFst X p (X.d ω) =
      supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p}
          (X.d (X.conj.twistProj (p - 1) (supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} ω))) -
        supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2}
          (X.d (X.conj.twistProj (p - 1) (supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} ω))) +
        2 • X.conj.twistProj p (supportedProj 𝒜 {i | p ≤ i.1 ∧ p ≤ i.2}
          (X.d (supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} ω))) := by
  -- `f = (π_Qbar - π_Q) ∘ d` anticommutes with conjugation, so it carries `π_{p-1}` to `π_p`.
  have e := X.conj.map_twistProj_of_conj_eq_neg X.conj
    (f := (supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p} - supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2}) ∘ₗ
      X.d)
    (fun y ↦ by simp only [LinearMap.comp_apply, LinearMap.sub_apply, map_sub,
      conj_supportedProj_mixed, conj_supportedProj_mixedBar, conj_d, neg_sub]) (p - 1)
    (supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} ω)
  rw [sub_add_cancel] at e
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, map_sub] at e
  rw [contractionFst_apply, contractionFst_apply, map_add, map_nsmul, d_twistProj, d_twistProj,
    supportedProj_low_d p ω, supportedProj_mixed_d p ω]
  simp only [map_add, map_sub]
  linear_combination (norm := abel) -e

/-- The commutator of `d` with the second component of the contraction. -/
private theorem d_contractionSnd_sub (p : ℤ) (ω : A) :
    X.d (contractionSnd X p ω) - contractionSnd X p (X.d ω) =
      2 • supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p}
          (X.d (X.conj.twistProj (p - 1) (supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} ω))) +
        2 • X.conj.twistProj p (supportedProj 𝒜 {i | p ≤ i.1 ∧ p ≤ i.2}
          (X.d (supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} ω))) := by
  set a := supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} ω
  have e₁ : 2 • X.conj.twistProj p (supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} (X.d a)) =
      supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} (X.d a) +
        p.negOnePow • supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p} (X.d (X.conj.toEquiv a)) := by
    rw [Conjugation.two_nsmul_twistProj, conj_supportedProj_mixed, conj_d]
  have e₂ : 2 • supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p} (X.d (X.conj.twistProj (p - 1) a)) =
      supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p} (X.d a) -
        p.negOnePow • supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p} (X.d (X.conj.toEquiv a)) := by
    rw [← map_nsmul, ← map_nsmul, Conjugation.two_nsmul_twistProj, Int.negOnePow_sub,
      Int.negOnePow_one, mul_neg_one, Units.neg_smul, map_add, map_add, map_neg, map_neg,
      LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, sub_eq_add_neg]
  rw [contractionSnd_apply, contractionSnd_apply, map_sub, map_sub, map_nsmul, d_twistProj,
    supportedProj_mixed_d p ω, supportedProj_hodge_d p ω]
  simp only [map_add, map_sub]
  linear_combination (norm := abel) -e₁ - e₂

/-- On the real twist `A_ℝ(p)`, the first component of the contraction is `r ↦ r - π_PP r`. -/
private theorem contractionFst_of_mem_twist {p : ℤ} {r : A} (hr : r ∈ X.conj.twist p) :
    contractionFst X p r = r - supportedProj 𝒜 {i | p ≤ i.1 ∧ p ≤ i.2} r := by
  have hL : supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} r ∈ X.conj.twist p :=
    X.conj.map_mem_twist X.conj (fun y ↦ conj_supportedProj_low p y) hr
  have hQ : 2 • X.conj.twistProj p (supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} r) =
      supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} r + supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p} r := by
    rw [Conjugation.two_nsmul_twistProj, conj_supportedProj_mixed, (Conjugation.mem_twist _).1 hr,
      LinearMap.map_smul_of_tower, smul_smul, Int.units_mul_self, one_smul]
  rw [contractionFst_apply, X.conj.twistProj_of_mem hL, hQ]
  linear_combination (norm := abel) supportedProj_partition 𝒜 p r

/-- On the real twist `A_ℝ(p)`, the second component of the contraction is `r ↦ -π_PP r`. -/
private theorem contractionSnd_of_mem_twist {p : ℤ} {r : A} (hr : r ∈ X.conj.twist p) :
    contractionSnd X p r = -supportedProj 𝒜 {i | p ≤ i.1 ∧ p ≤ i.2} r := by
  rw [contractionSnd_apply, Conjugation.two_nsmul_twistProj, conj_supportedProj_mixed,
    (Conjugation.mem_twist _).1 hr, LinearMap.map_smul_of_tower, smul_smul, Int.units_mul_self,
    one_smul, supportedProj_hodge 𝒜 p r]
  abel

/-- A projection onto types `(r, s)` with `r < p` kills a sum of type pieces with `p ≤ r`. -/
private theorem supportedProj_eq_zero_of_mem_hodge {p : ℤ} {P : ℤ × ℤ → Prop}
    {T : Set (ℤ × ℤ)} (hT : T ⊆ {i | p ≤ i.1}) {f : A} (hf : f ∈ ⨆ i : T, 𝒜 i) :
    supportedProj 𝒜 {i | i.1 < p ∧ P i} f = 0 :=
  supportedProj_eq_zero_of_disjoint
    (Set.disjoint_left.2 fun _ (h₁ : _ ∧ _) h₂ ↦ h₁.1.not_ge (hT h₂)) hf

/-- On `FᵖA`, the first component of the contraction vanishes. -/
private theorem contractionFst_of_mem_hodge {p : ℤ} {T : Set (ℤ × ℤ)} (hT : T ⊆ {i | p ≤ i.1})
    {f : A} (hf : f ∈ ⨆ i : T, 𝒜 i) : contractionFst X p f = 0 := by
  rw [contractionFst_apply, supportedProj_eq_zero_of_mem_hodge hT hf,
    supportedProj_eq_zero_of_mem_hodge hT hf]
  simp

/-- On `FᵖA`, the second component of the contraction is `f ↦ -f`. -/
private theorem contractionSnd_of_mem_hodge {p : ℤ} {T : Set (ℤ × ℤ)} (hT : T ⊆ {i | p ≤ i.1})
    {f : A} (hf : f ∈ ⨆ i : T, 𝒜 i) : contractionSnd X p f = -f := by
  rw [contractionSnd_apply, supportedProj_eq_zero_of_mem_hodge hT hf,
    supportedProj_eq_self_of_subset hT hf]
  simp

/-- The map `h d + d h + 1` of the Deligne cone, with `h` the contraction, on vectors `(r, f, ω)`
with `r ∈ A_ℝ(p)` and `f ∈ FᵖA`. Here `ξ = π_{p-1} π_L ω` and `z = 2 π_p π_PP d π_Q ω`. -/
private theorem contraction_deligneConeDiff_add {p : ℤ} {T : Set (ℤ × ℤ)}
    (hT : T ⊆ {i | p ≤ i.1}) {x : A × A × A} (hr : x.1 ∈ X.conj.twist p)
    (hf : x.2.1 ∈ ⨆ i : T, 𝒜 i) :
    X.deligneConeContraction p (X.deligneConeDiff x) +
        X.deligneConeDiff (X.deligneConeContraction p x) + x =
      (supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p}
          (X.d (X.conj.twistProj (p - 1) (supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} x.2.2))) -
        supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2}
          (X.d (X.conj.twistProj (p - 1) (supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} x.2.2))) +
        2 • X.conj.twistProj p (supportedProj 𝒜 {i | p ≤ i.1 ∧ p ≤ i.2}
          (X.d (supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} x.2.2))) +
        supportedProj 𝒜 {i | p ≤ i.1 ∧ p ≤ i.2} x.1,
      2 • supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p}
          (X.d (X.conj.twistProj (p - 1) (supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} x.2.2))) +
        2 • X.conj.twistProj p (supportedProj 𝒜 {i | p ≤ i.1 ∧ p ≤ i.2}
          (X.d (supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} x.2.2))) +
        supportedProj 𝒜 {i | p ≤ i.1 ∧ p ≤ i.2} x.1,
      X.conj.twistProj (p - 1) (supportedProj 𝒜 {i | i.1 < p ∧ i.2 < p} x.2.2)) := by
  obtain ⟨r, f, ω⟩ := x
  dsimp only at hr hf ⊢
  have h₁ := d_contractionFst_sub (X := X) p ω
  have h₂ := d_contractionSnd_sub (X := X) p ω
  have h₃ := contractionSnd_sub_contractionFst_add (X := X) p ω
  rw [deligneConeContraction_eq, deligneConeContraction_eq, deligneConeDiff_apply,
    deligneConeDiff_apply]
  simp only [map_sub, contractionFst_of_mem_hodge (X := X) hT hf,
    contractionSnd_of_mem_hodge (X := X) hT hf, contractionFst_of_mem_twist hr,
    contractionSnd_of_mem_twist hr, map_zero, sub_zero,
    Prod.mk_add_mk, Prod.mk.injEq] at h₁ h₂ h₃ ⊢
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (norm := abel) h₁
  · linear_combination (norm := abel) h₂
  · linear_combination (norm := abel) h₃


/-! ### The comparison maps on the terms -/

/-- The inclusion carries `Dⁿ(A, p)` into the term `Kⁿ` of the Deligne cone. -/
theorem deligneToConeMap_mem {p n : ℤ} {x : A} (hx : x ∈ X.delignePiece p n) :
    X.deligneToConeMap p n x ∈ X.deligneConePiece p n := by
  rcases lt_or_ge n (2 * p) with h | h
  · rw [mem_delignePiece_of_lt h] at hx
    have hdx : X.d x ∈ ⨆ i : {i : ℤ × ℤ | i.1 + i.2 = n}, 𝒜 i :=
      X.d_mem_iSup (by region_omega) hx.1
    -- `(π_Qbar - π_Q) ∘ d` anticommutes with conjugation, so it raises the real twist by one.
    have ht := X.conj.map_mem_twist_add_one X.conj
      (f := (supportedProj 𝒜 {i | p ≤ i.1 ∧ i.2 < p} - supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2}) ∘ₗ
        X.d)
      (fun y ↦ by simp only [LinearMap.comp_apply, LinearMap.sub_apply, map_sub,
        conj_supportedProj_mixed, conj_supportedProj_mixedBar, conj_d, neg_sub]) hx.2
    rw [sub_add_cancel] at ht
    have hF : ({i : ℤ × ℤ | p ≤ i.1 ∧ i.2 < p} ∩ {i | i.1 + i.2 = n}) ⊆
        {i | i.1 + i.2 = n ∧ p ≤ i.1} := fun i hi ↦ ⟨hi.2, hi.1.1⟩
    have hD : {i : ℤ × ℤ | i.1 + i.2 = n - 1 ∧ i.1 < p ∧ i.2 < p} ⊆ {i | i.1 + i.2 = n - 1} :=
      fun _ hi ↦ hi.1
    rw [deligneToConeMap_of_lt h, mem_deligneConePiece]
    exact ⟨⟨sub_mem (supportedProj_mem_iSup_of_mem hdx) (supportedProj_mem_iSup_of_mem hdx), ht⟩,
      nsmul_mem (mem_iSup_of_subset hF (supportedProj_mem_iSup_inter hdx)) 2,
      mem_iSup_of_subset hD hx.1⟩
  · rw [mem_delignePiece_of_le h] at hx
    have h₁ : {i : ℤ × ℤ | i.1 + i.2 = n ∧ p ≤ i.1 ∧ p ≤ i.2} ⊆ {i | i.1 + i.2 = n} :=
      fun _ hi ↦ hi.1
    have h₂ : {i : ℤ × ℤ | i.1 + i.2 = n ∧ p ≤ i.1 ∧ p ≤ i.2} ⊆ {i | i.1 + i.2 = n ∧ p ≤ i.1} :=
      fun _ hi ↦ ⟨hi.1, hi.2.1⟩
    rw [deligneToConeMap_of_le h, mem_deligneConePiece]
    exact ⟨⟨mem_iSup_of_subset h₁ hx.1, hx.2⟩, mem_iSup_of_subset h₂ hx.1, zero_mem _⟩

/-- The projection carries the term `Kⁿ` of the Deligne cone into `Dⁿ(A, p)`. -/
theorem coneToDeligneMap_mem {p n : ℤ} {x : A × A × A} (hx : x ∈ X.deligneConePiece p n) :
    X.coneToDeligneMap p n x ∈ X.delignePiece p n := by
  obtain ⟨⟨hr, hr'⟩, -, hω⟩ := mem_deligneConePiece.1 hx
  rcases lt_or_ge n (2 * p) with h | h
  · have hS : ∀ i ∈ {i : ℤ × ℤ | i.1 + i.2 = n - 1 ∧ i.1 < p ∧ i.2 < p},
        i.swap ∈ {i : ℤ × ℤ | i.1 + i.2 = n - 1 ∧ i.1 < p ∧ i.2 < p} := by
      region_omega
    have hL : ({i : ℤ × ℤ | i.1 < p ∧ i.2 < p} ∩ {i | i.1 + i.2 = n - 1}) ⊆
        {i | i.1 + i.2 = n - 1 ∧ i.1 < p ∧ i.2 < p} := fun _ hi ↦ ⟨hi.2, hi.1⟩
    rw [coneToDeligneMap_of_lt h, mem_delignePiece_of_lt h]
    exact ⟨X.twistProj_mem_iSup hS (p - 1)
      (mem_iSup_of_subset hL (supportedProj_mem_iSup_inter hω)), X.conj.twistProj_mem _ _⟩
  · have hdq : X.d (supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} x.2.2) ∈
        ⨆ i : {i : ℤ × ℤ | i.1 + i.2 = n}, 𝒜 i :=
      X.d_mem_iSup_degree (sub_add_cancel n 1) (supportedProj_mem_iSup_of_mem hω)
    have hS : ∀ i ∈ {i : ℤ × ℤ | i.1 + i.2 = n ∧ p ≤ i.1 ∧ p ≤ i.2},
        i.swap ∈ {i : ℤ × ℤ | i.1 + i.2 = n ∧ p ≤ i.1 ∧ p ≤ i.2} := by
      region_omega
    have hPP : ({i : ℤ × ℤ | p ≤ i.1 ∧ p ≤ i.2} ∩ {i | i.1 + i.2 = n}) ⊆
        {i | i.1 + i.2 = n ∧ p ≤ i.1 ∧ p ≤ i.2} := fun _ hi ↦ ⟨hi.2, hi.1⟩
    rw [coneToDeligneMap_of_le h, mem_delignePiece_of_le h]
    exact ⟨add_mem (mem_iSup_of_subset hPP (supportedProj_mem_iSup_inter hr))
        (nsmul_mem (X.twistProj_mem_iSup hS p
          (mem_iSup_of_subset hPP (supportedProj_mem_iSup_inter hdq))) 2),
      add_mem (X.conj.map_mem_twist X.conj (fun y ↦ conj_supportedProj_high p y) hr')
        (nsmul_mem (X.conj.twistProj_mem _ _) 2)⟩

/-- The contraction carries the term `Kⁿ⁺¹` of the Deligne cone into `Kⁿ`. -/
theorem deligneConeContraction_mem {p n : ℤ} {x : A × A × A}
    (hx : x ∈ X.deligneConePiece p (n + 1)) :
    X.deligneConeContraction p x ∈ X.deligneConePiece p n := by
  obtain ⟨-, -, hω⟩ := mem_deligneConePiece.1 hx
  rw [add_sub_cancel_right] at hω
  have hS : ∀ i ∈ {i : ℤ × ℤ | i.1 + i.2 = n}, i.swap ∈ {i : ℤ × ℤ | i.1 + i.2 = n} := by
    region_omega
  have hF : ({i : ℤ × ℤ | p ≤ i.1} ∩ {i | i.1 + i.2 = n}) ⊆ {i | i.1 + i.2 = n ∧ p ≤ i.1} :=
    fun _ hi ↦ ⟨hi.2, hi.1⟩
  have hF' : ({i : ℤ × ℤ | p ≤ i.1 ∧ i.2 < p} ∩ {i | i.1 + i.2 = n}) ⊆
      {i | i.1 + i.2 = n ∧ p ≤ i.1} := fun _ hi ↦ ⟨hi.2, hi.1.1⟩
  rw [deligneConeContraction_eq, mem_deligneConePiece]
  refine ⟨⟨?_, ?_⟩, ?_, zero_mem _⟩
  · rw [contractionFst_apply]
    exact add_mem (X.twistProj_mem_iSup hS p (supportedProj_mem_iSup_of_mem hω))
      (nsmul_mem (X.twistProj_mem_iSup hS p (supportedProj_mem_iSup_of_mem hω)) 2)
  · rw [contractionFst_apply]
    exact add_mem (X.conj.twistProj_mem _ _) (nsmul_mem (X.conj.twistProj_mem _ _) 2)
  · -- The second component is `(-1) ^ p` times the conjugate of `π_Q ω`, minus `π_F ω`.
    rw [contractionSnd_apply, Conjugation.two_nsmul_twistProj, add_sub_cancel_left,
      conj_supportedProj_mixed, Units.smul_def]
    exact sub_mem (zsmul_mem (mem_iSup_of_subset hF'
      (supportedProj_mem_iSup_inter (X.conj_mem_iSup hS hω))) _)
      (mem_iSup_of_subset hF (supportedProj_mem_iSup_inter hω))

/-- The inclusion of the Deligne complex into the Deligne cone commutes with the differentials. -/
theorem deligneConeDiff_deligneToConeMap {p n : ℤ} {x : A} (hx : x ∈ X.delignePiece p n) :
    X.deligneConeDiff (X.deligneToConeMap p n x) =
      X.deligneToConeMap p (n + 1) (X.deligneDiff p n x) := by
  rcases lt_trichotomy (n + 1) (2 * p) with h | h | h
  · rw [mem_delignePiece_of_lt (by omega)] at hx
    have hdx : X.d x ∈ ⨆ i : {i : ℤ × ℤ | i.1 + i.2 = n}, 𝒜 i :=
      X.d_mem_iSup (by region_omega) hx.1
    -- `d (π_S d x) = -π_S d π_L d x` for `S` the types `r < p ≤ s` or `s < p ≤ r`, since
    -- `d d x = 0` and `π_PP` vanishes in degree `n + 1 < 2p`.
    have hQ := supportedProj_mixed_d (X := X) p (X.d x)
    have hQ' := supportedProj_mixedBar_d (X := X) p (X.d x)
    rw [d_d, map_zero, supportedProj_high_eq_zero h (X.d_mem_iSup_degree rfl
      (supportedProj_mem_iSup_of_mem hdx)), sub_zero] at hQ hQ'
    have hpart := supportedProj_partition 𝒜 p (X.d x)
    rw [supportedProj_high_eq_zero (by omega) hdx, add_zero] at hpart
    rw [deligneToConeMap_of_lt (by omega), deligneToConeMap_of_lt h, deligneDiff_of_lt h,
      deligneConeDiff_apply]
    simp only [map_sub, map_nsmul, map_neg, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · linear_combination (norm := abel) -hQ' + hQ
    · linear_combination (norm := abel) (-2 : ℤ) • hQ'
    · linear_combination (norm := abel) hpart
  · obtain rfl : n = 2 * p - 1 := by omega
    obtain ⟨hx, -⟩ := mem_delignePiece_two_mul_sub_one_iff.1 hx
    have h₁ : (p, p - 1) ∈ {i : ℤ × ℤ | p ≤ i.1 ∧ i.2 < p} := ⟨le_rfl, sub_one_lt p⟩
    have h₂ : (p - 1, p) ∉ {i : ℤ × ℤ | p ≤ i.1 ∧ i.2 < p} := by
      region_omega
    have h₃ : (p, p - 1) ∉ {i : ℤ × ℤ | i.1 < p ∧ p ≤ i.2} := by
      region_omega
    have h₄ : (p - 1, p) ∈ {i : ℤ × ℤ | i.1 < p ∧ p ≤ i.2} := ⟨sub_one_lt p, le_rfl⟩
    have hdel := X.del_mem hx
    have hdelBar := X.delBar_mem hx
    rw [sub_add_cancel] at hdel hdelBar
    rw [deligneToConeMap_of_lt (by omega), deligneToConeMap_of_le h.ge, deligneDiff_of_eq h,
      deligneConeDiff_apply]
    simp only [d_apply, map_add, supportedProj_of_mem hdel h₁, supportedProj_of_notMem hdelBar h₂,
      supportedProj_of_notMem hdel h₃, supportedProj_of_mem hdelBar h₄, add_zero, zero_add,
      map_sub, map_nsmul, del_del, delBar_delBar, delBar_del, Prod.mk.injEq]
    refine ⟨by abel, by abel, by abel⟩
  · rw [deligneToConeMap_of_le (by omega), deligneToConeMap_of_le (by omega),
      deligneDiff_of_le (by omega), deligneConeDiff_apply]
    simp

/-- The projection after the inclusion is the identity of `Dⁿ(A, p)`. -/
theorem coneToDeligneMap_deligneToConeMap {p n : ℤ} {x : A} (hx : x ∈ X.delignePiece p n) :
    X.coneToDeligneMap p n (X.deligneToConeMap p n x) = x := by
  rcases lt_or_ge n (2 * p) with h | h
  · rw [mem_delignePiece_of_lt h] at hx
    have hL : {i : ℤ × ℤ | i.1 + i.2 = n - 1 ∧ i.1 < p ∧ i.2 < p} ⊆ {i | i.1 < p ∧ i.2 < p} :=
      fun _ hi ↦ hi.2
    rw [deligneToConeMap_of_lt h, coneToDeligneMap_of_lt h,
      supportedProj_eq_self_of_subset hL hx.1, X.conj.twistProj_of_mem hx.2]
  · rw [mem_delignePiece_of_le h] at hx
    have hPP : {i : ℤ × ℤ | i.1 + i.2 = n ∧ p ≤ i.1 ∧ p ≤ i.2} ⊆ {i | p ≤ i.1 ∧ p ≤ i.2} :=
      fun _ hi ↦ hi.2
    rw [deligneToConeMap_of_le h, coneToDeligneMap_of_le h,
      supportedProj_eq_self_of_subset hPP hx.1]
    simp

/-- On the Deligne cone, the inclusion after the projection is `h d + d h + 1`, where `h` is the
contraction `TauCeti.Hodge.DolbeaultComplex.deligneConeContraction`. -/
theorem deligneToConeMap_coneToDeligneMap {p n : ℤ} {x : A × A × A}
    (hx : x ∈ X.deligneConePiece p n) :
    X.deligneToConeMap p n (X.coneToDeligneMap p n x) =
      X.deligneConeContraction p (X.deligneConeDiff x) +
        X.deligneConeDiff (X.deligneConeContraction p x) + x := by
  obtain ⟨⟨hr, hr'⟩, hf, hω⟩ := mem_deligneConePiece.1 hx
  have hF : {i : ℤ × ℤ | i.1 + i.2 = n ∧ p ≤ i.1} ⊆ {i | p ≤ i.1} := fun _ hi ↦ hi.2
  rw [contraction_deligneConeDiff_add hF hr' hf]
  have hdq : X.d (supportedProj 𝒜 {i | i.1 < p ∧ p ≤ i.2} x.2.2) ∈
      ⨆ i : {i : ℤ × ℤ | i.1 + i.2 = n}, 𝒜 i :=
    X.d_mem_iSup_degree (sub_add_cancel n 1) (supportedProj_mem_iSup_of_mem hω)
  rcases lt_or_ge n (2 * p) with h | h
  · rw [coneToDeligneMap_of_lt h, deligneToConeMap_of_lt h, supportedProj_high_eq_zero h hdq,
      supportedProj_high_eq_zero h hr]
    simp
  · rw [coneToDeligneMap_of_le h, deligneToConeMap_of_le h,
      supportedProj_low_eq_zero (by omega) hω]
    simp [add_comm]

/-- The projection of the Deligne cone onto the Deligne complex commutes with the
differentials. -/
theorem coneToDeligneMap_deligneConeDiff {p n : ℤ} {x : A × A × A}
    (hx : x ∈ X.deligneConePiece p n) :
    X.coneToDeligneMap p (n + 1) (X.deligneConeDiff x) =
      X.deligneDiff p n (X.coneToDeligneMap p n x) := by
  -- Both sides lie in `Dⁿ⁺¹(A, p)`, on which the inclusion is injective, and both have the same
  -- image `d h d x + d x` under the inclusion.
  have hDx := deligneConeDiff_mem hx
  have hψ := coneToDeligneMap_mem hx
  have h : X.deligneToConeMap p (n + 1) (X.coneToDeligneMap p (n + 1) (X.deligneConeDiff x)) =
      X.deligneToConeMap p (n + 1) (X.deligneDiff p n (X.coneToDeligneMap p n x)) := by
    rw [← deligneConeDiff_deligneToConeMap hψ, deligneToConeMap_coneToDeligneMap hx,
      deligneToConeMap_coneToDeligneMap hDx]
    simp only [map_add, deligneConeDiff_deligneConeDiff, map_zero, zero_add, add_zero]
  rw [← coneToDeligneMap_deligneToConeMap (coneToDeligneMap_mem hDx), h,
    coneToDeligneMap_deligneToConeMap (deligneDiff_mem hψ)]


/-! ### The comparison of complexes -/

variable (X)

/-- The inclusion `D(A, p) ⟶ K` of the Deligne complex into the Deligne cone: in each degree, the
restriction of `TauCeti.Hodge.DolbeaultComplex.deligneToConeMap`. -/
noncomputable def deligneToCone (p : ℤ) : X.deligneComplex p ⟶ X.deligneCone p :=
  CochainComplex.ofHom
    (fun n ↦ ModuleCat.ofHom (LinearMap.restrict (p := X.delignePiece p n)
      (q := X.deligneConePiece p n) ((X.deligneToConeMap p n).restrictScalars ℝ)
      fun _ hx ↦ deligneToConeMap_mem hx))
    fun n ↦ by
      ext x
      simp only [deligneComplex, deligneCone, CochainComplex.of_d, ModuleCat.hom_comp,
        ModuleCat.hom_ofHom]
      exact Subtype.ext (deligneConeDiff_deligneToConeMap x.property)

/-- The projection `K ⟶ D(A, p)` of the Deligne cone onto the Deligne complex: in each degree,
the restriction of `TauCeti.Hodge.DolbeaultComplex.coneToDeligneMap`. -/
noncomputable def coneToDeligne (p : ℤ) : X.deligneCone p ⟶ X.deligneComplex p :=
  CochainComplex.ofHom
    (fun n ↦ ModuleCat.ofHom (LinearMap.restrict (p := X.deligneConePiece p n)
      (q := X.delignePiece p n) (X.coneToDeligneMap p n) fun _ hx ↦ coneToDeligneMap_mem hx))
    fun n ↦ by
      ext x
      simp only [deligneComplex, deligneCone, CochainComplex.of_d, ModuleCat.hom_comp,
        ModuleCat.hom_ofHom]
      exact Subtype.ext (coneToDeligneMap_deligneConeDiff x.property).symm

/-- In each degree, the inclusion into the Deligne cone is
`TauCeti.Hodge.DolbeaultComplex.deligneToConeMap`. -/
@[simp]
theorem deligneToCone_f_apply (p n : ℤ) (x : X.delignePiece p n) :
    Subtype.val (p := (· ∈ X.deligneConePiece p n)) ((X.deligneToCone p).f n x) =
      X.deligneToConeMap p n x :=
  (rfl)

/-- In each degree, the projection onto the Deligne complex is
`TauCeti.Hodge.DolbeaultComplex.coneToDeligneMap`. -/
@[simp]
theorem coneToDeligne_f_apply (p n : ℤ) (x : X.deligneConePiece p n) :
    Subtype.val (p := (· ∈ X.delignePiece p n)) ((X.coneToDeligne p).f n x) =
      X.coneToDeligneMap p n x :=
  (rfl)

/-- The projection after the inclusion is the identity of the Deligne complex. -/
@[reassoc (attr := simp)]
theorem deligneToCone_comp_coneToDeligne (p : ℤ) :
    X.deligneToCone p ≫ X.coneToDeligne p = 𝟙 (X.deligneComplex p) := by
  ext n x
  exact Subtype.ext (coneToDeligneMap_deligneToConeMap x.property)

/-- The components `Kⁿ ⟶ Kᵐ` of the homotopy: the contraction when `m + 1 = n`, and `0`
otherwise. -/
private noncomputable def coneHomotopyHom (p n m : ℤ) :
    (X.deligneCone p).X n ⟶ (X.deligneCone p).X m :=
  if h : m + 1 = n then
    (ModuleCat.ofHom (LinearMap.restrict (p := X.deligneConePiece p n)
      (q := X.deligneConePiece p m) (X.deligneConeContraction p) fun _ hx ↦
        deligneConeContraction_mem (h ▸ hx)) : (X.deligneCone p).X n ⟶ (X.deligneCone p).X m)
  else 0

private theorem coneHomotopyHom_apply {p n m : ℤ} (h : m + 1 = n) (x : X.deligneConePiece p n) :
    Subtype.val (p := (· ∈ X.deligneConePiece p m)) (coneHomotopyHom X p n m x) =
      X.deligneConeContraction p x := by
  subst h
  simp only [coneHomotopyHom, ↓reduceDIte]
  rfl

/-- The homotopy `h d + d h` from the inclusion after the projection to the identity of the
Deligne cone, where `h` is the contraction
`TauCeti.Hodge.DolbeaultComplex.deligneConeContraction`. -/
noncomputable def deligneConeHomotopy (p : ℤ) :
    Homotopy (X.coneToDeligne p ≫ X.deligneToCone p) (𝟙 (X.deligneCone p)) where
  hom := coneHomotopyHom X p
  zero n m h := dite_eq_right h
  comm n := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n from sub_add_cancel n 1)]
    ext (x : X.deligneConePiece p n)
    have e₁ : Subtype.val (p := (· ∈ X.deligneConePiece p n))
        (coneHomotopyHom X p (n + 1) n ((X.deligneCone p).d n (n + 1) x)) =
          X.deligneConeContraction p (X.deligneConeDiff x) :=
      (coneHomotopyHom_apply X rfl _).trans (congrArg _ (deligneCone_d_apply X p rfl x))
    have e₂ : Subtype.val (p := (· ∈ X.deligneConePiece p n))
        ((X.deligneCone p).d (n - 1) n (coneHomotopyHom X p n (n - 1) x)) =
          X.deligneConeDiff (X.deligneConeContraction p x) :=
      (deligneCone_d_apply X p (sub_add_cancel n 1) _).trans
        (congrArg _ (coneHomotopyHom_apply X (sub_add_cancel n 1) x))
    -- The terms of the cone are only definitionally the subtypes `deligneConePiece`, so the
    -- identity `deligneToConeMap_coneToDeligneMap` of their values is applied up to unfolding.
    exact Subtype.ext ((deligneToConeMap_coneToDeligneMap x.property).trans
      (by rw [← e₁, ← e₂]; rfl))

/-- Between degrees `n` and `m = n - 1`, the homotopy of the Deligne cone is the restriction of
the contraction `TauCeti.Hodge.DolbeaultComplex.deligneConeContraction`. -/
theorem deligneConeHomotopy_hom_apply (p : ℤ) {n m : ℤ} (h : m + 1 = n)
    (x : X.deligneConePiece p n) :
    Subtype.val (p := (· ∈ X.deligneConePiece p m)) ((X.deligneConeHomotopy p).hom n m x) =
      X.deligneConeContraction p x :=
  coneHomotopyHom_apply X h x

/-- Outside the degrees `n` and `m = n - 1`, the homotopy of the Deligne cone vanishes. -/
theorem deligneConeHomotopy_hom_eq_zero (p : ℤ) {n m : ℤ} (h : ¬m + 1 = n) :
    (X.deligneConeHomotopy p).hom n m = 0 :=
  (X.deligneConeHomotopy p).zero n m h

/-- The Deligne complex `D(A, p)` is homotopy equivalent to the Deligne cone
`fib(A_ℝ(p) ⊕ FᵖA → A)`, through the inclusion `TauCeti.Hodge.DolbeaultComplex.deligneToCone`
and the projection `TauCeti.Hodge.DolbeaultComplex.coneToDeligne`, whose composite on the Deligne
complex is the identity. -/
noncomputable def deligneHomotopyEquivCone (p : ℤ) :
    HomotopyEquiv (X.deligneComplex p) (X.deligneCone p) where
  hom := X.deligneToCone p
  inv := X.coneToDeligne p
  homotopyHomInvId := Homotopy.ofEq (X.deligneToCone_comp_coneToDeligne p)
  homotopyInvHomId := X.deligneConeHomotopy p

/-- The homotopy equivalence with the Deligne cone is the inclusion
`TauCeti.Hodge.DolbeaultComplex.deligneToCone`. -/
@[simp]
theorem deligneHomotopyEquivCone_hom (p : ℤ) :
    (X.deligneHomotopyEquivCone p).hom = X.deligneToCone p :=
  (rfl)

/-- The inverse of the homotopy equivalence with the Deligne cone is the projection
`TauCeti.Hodge.DolbeaultComplex.coneToDeligne`. -/
@[simp]
theorem deligneHomotopyEquivCone_inv (p : ℤ) :
    (X.deligneHomotopyEquivCone p).inv = X.coneToDeligne p :=
  (rfl)

end Decomposition

end DolbeaultComplex

end TauCeti.Hodge
