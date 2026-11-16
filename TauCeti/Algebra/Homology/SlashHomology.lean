/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import TauCeti.Algebra.Homology.SquareZero

/-!
# Slash homology of `p`-differential modules

A linear endomorphism `d` of a module `M` satisfying `d ^ p = 0` is an ungraded `p`-complex
(an `N`-complex in Kapranov's sense when `p = N`). Unlike a square-zero differential, which has a
single homology group `ker d / im d`, a `p`-differential admits `p - 1` **slash homology** groups
indexed by `0 ≤ j ≤ p - 2`:

`H^{/j}(M) = ker(d ^ (j + 1)) / (im(d ^ (p - j - 1)) + ker(d ^ j))`.

When `d ^ p = 0`, both `im(d ^ (p - j - 1))` and `ker(d ^ j)` lie inside `ker(d ^ (j + 1))`, so
the denominator is a genuine submodule of the slash cycles `ker(d ^ (j + 1))`. At `p = 2` and
`j = 0`, `SlashHomology 2 d 0` recovers the ordinary homology `ker d / im d` of a square-zero
endomorphism (`SlashHomology.twoZeroEquivHomology`).

A linear map `f : M → N` commuting with the `p`-differentials induces a map on every slash
homology group. Any contracting operator `h : M → N` determines the `p`-null-homotopic chain map
`∑ i ∈ Finset.range p, d_N ^ i ∘ h ∘ d_M ^ (p - 1 - i)`, which acts as zero on all slash homology
groups; consequently `p`-homotopic chain maps induce equal maps on `SlashHomology`.

Vanishing of all `p - 1` slash homology groups characterizes the exact filtrations
`ker(d ^ m) = im(d ^ (p - m))` for `0 ≤ m ≤ p`. Over a field, this exactness constructs a
monomial basis `(i, r) ↦ d ^ r (b i)` of `M` over a complement of `im d` without any
finite-dimensionality hypothesis (`SlashHomology.exists_basis_pow_of_forall_subsingleton`), and for
finite-dimensional `M` yields Khovanov–Qi's dimension decomposition
`dim M = p · dim(im(d ^ (p - 1))) + ∑_{j = 0}^{p - 2} dim H^{/j}(M)`.

## Main definitions

* `TauCeti.SlashHomology`: the `j`-th slash homology module
  `ker(d ^ (j + 1)) ⧸ (im(d ^ (p - j - 1)) ⊔ ker(d ^ j))` of an endomorphism `d`.
* `TauCeti.SlashHomology.boundaries`: the slash-boundary submodule inside `ker(d ^ (j + 1))`.
* `TauCeti.SlashHomology.π`: the quotient projection from `ker(d ^ (j + 1))` to `SlashHomology`.
* `TauCeti.SlashHomology.map`, `TauCeti.SlashHomology.equiv`, `TauCeti.SlashHomology.prodEquiv`:
  functoriality and product compatibility of slash homology.
* `TauCeti.SlashHomology.nullHomotopicMap` and `TauCeti.SlashHomology.IsPHomotopic`: `p`-null
  chain maps `∑_{i = 0}^{p - 1} d_N ^ i ∘ h ∘ d_M ^ (p - 1 - i)` and the `p`-chain homotopy
  relation.
* `TauCeti.SlashHomology.twoZeroEquivHomology`: for `d ∘ d = 0`, the linear equivalence
  `SlashHomology 2 d 0 ≃ₗ[R] d.homology hd`.

## Main results

* `TauCeti.SlashHomology.range_sup_ker_le_ker`: when `d ^ p = 0`, the denominator
  `im(d ^ (p - j - 1)) ⊔ ker(d ^ j)` is contained in `ker(d ^ (j + 1))`.
* `TauCeti.SlashHomology.map_nullHomotopicMap` and `TauCeti.SlashHomology.map_eq_of_isPHomotopic`:
  homotopy invariance of slash homology.
* `TauCeti.SlashHomology.forall_subsingleton_iff_ker_pow_eq_range_pow`: when `d ^ p = 0`, all
  `SlashHomology p d j` with `j + 1 < p` vanish iff `ker(d ^ m) = im(d ^ (p - m))` for all `m ≤ p`.
* `TauCeti.SlashHomology.exists_basis_pow_of_forall_subsingleton`: over a field, vanishing slash
  homology produces a `k`-basis of the form `(i, r) ↦ (d ^ r) (v i)`.
* `TauCeti.SlashHomology.finrank_eq_mul_finrank_range_pow_add_sum`: Khovanov–Qi's dimension
  identity `finrank M = p * finrank (range (d ^ (p - 1))) + ∑_{j < p - 1} finrank H^{/j}(M)`.

## References

* M. Kapranov, *On the q-analog of homological algebra*, arXiv:q-alg/9611005, 1996.
* M. Khovanov, *Hopfological algebra and categorification at a root of unity: the first steps*,
  J. Knot Theory Ramifications **25** (2016), no. 3, 1640006.
* M. Khovanov and Y. Qi, *An approach to categorification of some small quantum groups*,
  Quantum Topol. **6** (2015), 185–311, §2 (slash homology and equation (20)).
-/

public section

namespace TauCeti

section Ring

variable {R M N P : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- The slash homology `H^{/j}(M) = ker(d ^ (j + 1)) / (im(d ^ (p - j - 1)) + ker(d ^ j))` of a
linear endomorphism `d`, realized as a quotient of the slash cycles `ker(d ^ (j + 1))`
(Khovanov–Qi, §2). -/
abbrev SlashHomology (p : ℕ) (d : M →ₗ[R] M) (j : ℕ) : Type _ :=
  LinearMap.ker (d ^ (j + 1)) ⧸
    (LinearMap.range (d ^ (p - j - 1)) ⊔ LinearMap.ker (d ^ j)).comap
      (LinearMap.ker (d ^ (j + 1))).subtype

namespace SlashHomology

/-- The submodule of `ker(d ^ (j + 1))` cut out by `im(d ^ (p - j - 1)) ⊔ ker(d ^ j)`. -/
abbrev boundaries (p : ℕ) (d : M →ₗ[R] M) (j : ℕ) :
    Submodule R (LinearMap.ker (d ^ (j + 1))) :=
  (LinearMap.range (d ^ (p - j - 1)) ⊔ LinearMap.ker (d ^ j)).comap
    (LinearMap.ker (d ^ (j + 1))).subtype

/-- Membership in `boundaries` is membership of the underlying vector in
`im(d ^ (p - j - 1)) ⊔ ker(d ^ j)`. -/
theorem mem_boundaries {p : ℕ} {d : M →ₗ[R] M} {j : ℕ}
    {z : LinearMap.ker (d ^ (j + 1))} :
    z ∈ boundaries p d j ↔
      (z : M) ∈ LinearMap.range (d ^ (p - j - 1)) ⊔ LinearMap.ker (d ^ j) :=
  Iff.rfl

/-- The quotient map sending a slash cycle `z ∈ ker(d ^ (j + 1))` to its slash homology class. -/
noncomputable def π (p : ℕ) (d : M →ₗ[R] M) (j : ℕ) :
    LinearMap.ker (d ^ (j + 1)) →ₗ[R] SlashHomology p d j :=
  (boundaries p d j).mkQ

/-- Evaluation of `SlashHomology.π` on a slash cycle. -/
@[simp]
theorem π_apply (p : ℕ) (d : M →ₗ[R] M) (j : ℕ) (z : LinearMap.ker (d ^ (j + 1))) :
    π p d j z = Submodule.Quotient.mk z :=
  (rfl)

/-- Every slash homology class is represented by a slash cycle in `ker(d ^ (j + 1))`. -/
theorem π_surjective (p : ℕ) (d : M →ₗ[R] M) (j : ℕ) :
    Function.Surjective (π p d j) :=
  Submodule.mkQ_surjective _

/-- A slash cycle represents the zero class iff it lies in `im(d ^ (p - j - 1)) ⊔ ker(d ^ j)`. -/
theorem π_eq_zero_iff {p : ℕ} {d : M →ₗ[R] M} {j : ℕ}
    (z : LinearMap.ker (d ^ (j + 1))) :
    π p d j z = 0 ↔
      (z : M) ∈ LinearMap.range (d ^ (p - j - 1)) ⊔ LinearMap.ker (d ^ j) :=
  Submodule.Quotient.mk_eq_zero _

/-- When `d ^ p = 0`, the image `im(d ^ (p - j - 1))` lies inside `ker(d ^ (j + 1))`. -/
theorem range_pow_le_ker_pow {p : ℕ} {d : M →ₗ[R] M} (hd : d ^ p = 0) (j : ℕ) :
    LinearMap.range (d ^ (p - j - 1)) ≤ LinearMap.ker (d ^ (j + 1)) := by
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.mem_ker, ← mul_apply_eq_comp, ← pow_add,
    pow_eq_zero_of_le (by omega : p ≤ j + 1 + (p - j - 1)) hd, LinearMap.zero_apply]

/-- The kernel `ker(d ^ j)` is always contained in `ker(d ^ (j + 1))`. -/
theorem ker_pow_le_ker_pow_succ (d : M →ₗ[R] M) (j : ℕ) :
    LinearMap.ker (d ^ j) ≤ LinearMap.ker (d ^ (j + 1)) := by
  intro x hx
  rw [LinearMap.mem_ker, pow_succ', mul_apply_eq_comp, LinearMap.mem_ker.mp hx, _root_.map_zero]

/-- **Denominator containment.** When `d ^ p = 0`, the denominator
`im(d ^ (p - j - 1)) ⊔ ker(d ^ j)` of `SlashHomology p d j` is contained in the numerator
`ker(d ^ (j + 1))`. -/
theorem range_sup_ker_le_ker {p : ℕ} {d : M →ₗ[R] M} (hd : d ^ p = 0) (j : ℕ) :
    LinearMap.range (d ^ (p - j - 1)) ⊔ LinearMap.ker (d ^ j) ≤
      LinearMap.ker (d ^ (j + 1)) :=
  sup_le (range_pow_le_ker_pow hd j) (ker_pow_le_ker_pow_succ d j)

/-- `SlashHomology p d j` is a subsingleton iff `ker(d ^ (j + 1))` is contained in
`im(d ^ (p - j - 1)) ⊔ ker(d ^ j)`. -/
theorem subsingleton_iff {p : ℕ} {d : M →ₗ[R] M} {j : ℕ} :
    Subsingleton (SlashHomology p d j) ↔
      LinearMap.ker (d ^ (j + 1)) ≤
        LinearMap.range (d ^ (p - j - 1)) ⊔ LinearMap.ker (d ^ j) := by
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  exact ⟨fun h x hx ↦ h (Submodule.mem_top (x := ⟨x, hx⟩)),
    fun h ⟨x, hx⟩ _ ↦ h hx⟩

/-- When `d ^ p = 0`, `SlashHomology p d j` vanishes iff the slash cycles equal the slash
boundaries: `ker(d ^ (j + 1)) = im(d ^ (p - j - 1)) ⊔ ker(d ^ j)`. -/
theorem subsingleton_iff_ker_eq {p : ℕ} {d : M →ₗ[R] M} (hd : d ^ p = 0) (j : ℕ) :
    Subsingleton (SlashHomology p d j) ↔
      LinearMap.ker (d ^ (j + 1)) =
        LinearMap.range (d ^ (p - j - 1)) ⊔ LinearMap.ker (d ^ j) :=
  subsingleton_iff.trans ⟨fun h ↦ le_antisymm h (range_sup_ker_le_ker hd j), le_of_eq⟩

/-! ### Functoriality and products -/

/-- A linear map intertwining `d` and `e` intertwines all powers `d ^ r` and `e ^ r`. -/
theorem comp_pow_of_comp_eq {d : M →ₗ[R] M} {e : N →ₗ[R] N} (f : M →ₗ[R] N)
    (hf : f ∘ₗ d = e ∘ₗ f) (r : ℕ) : f ∘ₗ (d ^ r) = (e ^ r) ∘ₗ f := by
  induction r with
  | zero => simp [Module.End.one_eq_id]
  | succ r ih =>
    rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc, hf, ← LinearMap.comp_assoc]

/-- A linear map `f : M → N` intertwining `d` and `e` (`f ∘ d = e ∘ f`) induces a linear map on
slash homology in every degree `j`. -/
noncomputable def map (p : ℕ) {d : M →ₗ[R] M} {e : N →ₗ[R] N} (f : M →ₗ[R] N)
    (hf : f ∘ₗ d = e ∘ₗ f) (j : ℕ) : SlashHomology p d j →ₗ[R] SlashHomology p e j :=
  (boundaries p d j).mapQ (boundaries p e j)
    (f.restrict fun _ ↦ LinearMap.map_mem_ker_of_comp_eq f
      (comp_pow_of_comp_eq f hf (j + 1))) <| by
    rintro z hz
    rw [Submodule.mem_comap, mem_boundaries, LinearMap.coe_restrict_apply]
    rcases Submodule.mem_sup.mp (mem_boundaries.mp hz) with ⟨u, ⟨x, rfl⟩, v, hv, huv⟩
    rw [← huv, _root_.map_add]
    refine Submodule.add_mem_sup ⟨f x, ?_⟩
      (LinearMap.map_mem_ker_of_comp_eq f (comp_pow_of_comp_eq f hf j) hv)
    simpa using (LinearMap.congr_fun (comp_pow_of_comp_eq f hf (p - j - 1)) x).symm

/-- `SlashHomology.map` sends the class of a slash cycle `z` to the class of `f z`. -/
@[simp]
theorem map_mk (p : ℕ) {d : M →ₗ[R] M} {e : N →ₗ[R] N} (f : M →ₗ[R] N)
    (hf : f ∘ₗ d = e ∘ₗ f) (j : ℕ) (z : LinearMap.ker (d ^ (j + 1))) :
    map p f hf j (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨f z, LinearMap.map_mem_ker_of_comp_eq f
        (comp_pow_of_comp_eq f hf (j + 1)) z.2⟩ :=
  (rfl)

/-- The identity map induces the identity on slash homology. -/
@[simp]
theorem map_id (p : ℕ) (d : M →ₗ[R] M) (j : ℕ) :
    map p LinearMap.id (by simp : LinearMap.id ∘ₗ d = d ∘ₗ LinearMap.id) j = LinearMap.id := by
  ext z
  simp

/-- The zero map induces the zero map on slash homology. -/
@[simp]
theorem map_zero (p : ℕ) (d : M →ₗ[R] M) (e : N →ₗ[R] N) (j : ℕ) :
    map p (0 : M →ₗ[R] N) (by simp : (0 : M →ₗ[R] N) ∘ₗ d = e ∘ₗ 0) j = 0 := by
  ext z
  simp

/-- `SlashHomology.map` is additive in the intertwining map. -/
@[simp]
theorem map_add (p : ℕ) {d : M →ₗ[R] M} {e : N →ₗ[R] N} (f g : M →ₗ[R] N)
    (hf : f ∘ₗ d = e ∘ₗ f) (hg : g ∘ₗ d = e ∘ₗ g) (j : ℕ) :
    map p (f + g) (by rw [LinearMap.add_comp, LinearMap.comp_add, hf, hg]) j =
      map p f hf j + map p g hg j := by
  ext z
  simp [← Submodule.Quotient.mk_add]

/-- `SlashHomology.map` commutes with negation. -/
@[simp]
theorem map_neg (p : ℕ) {d : M →ₗ[R] M} {e : N →ₗ[R] N} (f : M →ₗ[R] N)
    (hf : f ∘ₗ d = e ∘ₗ f) (j : ℕ) :
    map p (-f) (by rw [LinearMap.neg_comp, LinearMap.comp_neg, hf]) j = -map p f hf j := by
  ext z
  simp [← Submodule.Quotient.mk_neg, Submodule.Quotient.eq]

/-- `SlashHomology.map` commutes with subtraction. -/
@[simp]
theorem map_sub (p : ℕ) {d : M →ₗ[R] M} {e : N →ₗ[R] N} (f g : M →ₗ[R] N)
    (hf : f ∘ₗ d = e ∘ₗ f) (hg : g ∘ₗ d = e ∘ₗ g) (j : ℕ) :
    map p (f - g) (by rw [LinearMap.sub_comp, LinearMap.comp_sub, hf, hg]) j =
      map p f hf j - map p g hg j := by
  ext z
  simp [← Submodule.Quotient.mk_sub, Submodule.Quotient.eq]

/-- `SlashHomology.map` preserves composition of intertwining maps. -/
theorem map_comp (p : ℕ) {d : M →ₗ[R] M} {e : N →ₗ[R] N} {q : P →ₗ[R] P}
    (g : N →ₗ[R] P) (f : M →ₗ[R] N) (hf : f ∘ₗ d = e ∘ₗ f) (hg : g ∘ₗ e = q ∘ₗ g) (j : ℕ) :
    map p (g ∘ₗ f)
        (by rw [LinearMap.comp_assoc, hf, ← LinearMap.comp_assoc, hg, LinearMap.comp_assoc]) j =
      map p g hg j ∘ₗ map p f hf j := by
  ext z
  simp

/-- Simp-oriented composition law for `SlashHomology.map`. -/
@[simp]
theorem map_comp_map (p : ℕ) {d : M →ₗ[R] M} {e : N →ₗ[R] N} {q : P →ₗ[R] P}
    (g : N →ₗ[R] P) (f : M →ₗ[R] N) (hf : f ∘ₗ d = e ∘ₗ f) (hg : g ∘ₗ e = q ∘ₗ g) (j : ℕ) :
    map p g hg j ∘ₗ map p f hf j =
      map p (g ∘ₗ f)
        (by rw [LinearMap.comp_assoc, hf, ← LinearMap.comp_assoc, hg, LinearMap.comp_assoc]) j :=
  (map_comp p g f hf hg j).symm

/-- A linear equivalence intertwining `d` and `e` induces a linear equivalence on slash
homology. -/
noncomputable def equiv (p : ℕ) {d : M →ₗ[R] M} {e : N →ₗ[R] N} (f : M ≃ₗ[R] N)
    (hf : f.toLinearMap ∘ₗ d = e ∘ₗ f.toLinearMap) (j : ℕ) :
    SlashHomology p d j ≃ₗ[R] SlashHomology p e j :=
  have hf' : f.symm.toLinearMap ∘ₗ e = d ∘ₗ f.symm.toLinearMap := by
    ext y
    apply f.injective
    simpa using (LinearMap.congr_fun hf (f.symm y)).symm
  LinearEquiv.ofLinearMap (map p f.toLinearMap hf j) (map p f.symm.toLinearMap hf' j)
    (by ext z; simp) (by ext z; simp)

/-- `SlashHomology.equiv` acts on cycle classes via `SlashHomology.map`. -/
@[simp]
theorem equiv_mk (p : ℕ) {d : M →ₗ[R] M} {e : N →ₗ[R] N} (f : M ≃ₗ[R] N)
    (hf : f.toLinearMap ∘ₗ d = e ∘ₗ f.toLinearMap) (j : ℕ)
    (z : LinearMap.ker (d ^ (j + 1))) :
    equiv p f hf j (Submodule.Quotient.mk z) =
      map p f.toLinearMap hf j (Submodule.Quotient.mk z) :=
  (rfl)

/-- Slash homology of a product endomorphism `d.prodMap e` is the product of the slash
homologies. -/
noncomputable def prodEquiv (p : ℕ) (d : M →ₗ[R] M) (e : N →ₗ[R] N) (j : ℕ) :
    SlashHomology p (d.prodMap e) j ≃ₗ[R] SlashHomology p d j × SlashHomology p e j :=
  let inlComm : LinearMap.inl R M N ∘ₗ d = d.prodMap e ∘ₗ LinearMap.inl R M N :=
    LinearMap.ext fun x ↦ by simp
  let inrComm : LinearMap.inr R M N ∘ₗ e = d.prodMap e ∘ₗ LinearMap.inr R M N :=
    LinearMap.ext fun y ↦ by simp
  let fstComm : LinearMap.fst R M N ∘ₗ d.prodMap e = d ∘ₗ LinearMap.fst R M N :=
    LinearMap.ext fun ⟨_, _⟩ ↦ by simp
  let sndComm : LinearMap.snd R M N ∘ₗ d.prodMap e = e ∘ₗ LinearMap.snd R M N :=
    LinearMap.ext fun ⟨_, _⟩ ↦ by simp
  let inlFstComm :
      (LinearMap.inl R M N ∘ₗ LinearMap.fst R M N) ∘ₗ d.prodMap e =
        d.prodMap e ∘ₗ (LinearMap.inl R M N ∘ₗ LinearMap.fst R M N) :=
    LinearMap.ext fun ⟨_, _⟩ ↦ by simp
  let inrSndComm :
      (LinearMap.inr R M N ∘ₗ LinearMap.snd R M N) ∘ₗ d.prodMap e =
        d.prodMap e ∘ₗ (LinearMap.inr R M N ∘ₗ LinearMap.snd R M N) :=
    LinearMap.ext fun ⟨_, _⟩ ↦ by simp
  LinearEquiv.ofLinearMap
    ((map p (LinearMap.fst R M N) fstComm j).prod (map p (LinearMap.snd R M N) sndComm j))
    ((map p (LinearMap.inl R M N) inlComm j).coprod (map p (LinearMap.inr R M N) inrComm j))
    (LinearMap.ext fun ⟨c₁, c₂⟩ ↦ by
      obtain ⟨z₁, rfl⟩ := π_surjective p d j c₁
      obtain ⟨z₂, rfl⟩ := π_surjective p e j c₂
      simp)
    (by
      ext z
      have hdecomp :
          LinearMap.inl R M N ∘ₗ LinearMap.fst R M N +
            LinearMap.inr R M N ∘ₗ LinearMap.snd R M N = LinearMap.id :=
        LinearMap.ext fun ⟨_, _⟩ ↦ by simp
      have hsum := map_add p (LinearMap.inl R M N ∘ₗ LinearMap.fst R M N)
        (LinearMap.inr R M N ∘ₗ LinearMap.snd R M N) inlFstComm inrSndComm j
      simpa [← map_comp_map, hdecomp] using
        LinearMap.congr_fun hsum.symm (Submodule.Quotient.mk z))

/-! ### Comparison with ordinary homology at `p = 2` -/

/-- **Comparison with square-zero homology.** At `p = 2` and `j = 0`, slash homology of a
square-zero endomorphism `d` (`d ∘ d = 0`) is canonically isomorphic to its ordinary homology
`d.homology hd = ker d ⧸ im d`. -/
noncomputable def twoZeroEquivHomology (d : M →ₗ[R] M) (hd : d ∘ₗ d = 0) :
    SlashHomology 2 d 0 ≃ₗ[R] d.homology hd := by
  let E : LinearMap.ker (d ^ (0 + 1)) ≃ₗ[R] LinearMap.ker d :=
    LinearEquiv.ofEq _ _ (by simp)
  refine Submodule.Quotient.equiv (boundaries 2 d 0) d.boundariesInKer E ?_
  ext z
  simp [E, Module.End.one_eq_id]

/-- `twoZeroEquivHomology` sends the slash-homology class of a cycle `z` to its ordinary homology
class. -/
@[simp]
theorem twoZeroEquivHomology_mk (d : M →ₗ[R] M) (hd : d ∘ₗ d = 0)
    (z : LinearMap.ker (d ^ (0 + 1))) :
    twoZeroEquivHomology d hd (Submodule.Quotient.mk z) =
      d.homologyπ hd ⟨z.1, by simpa using z.2⟩ := by
  simp only [twoZeroEquivHomology, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply,
    LinearMap.homologyπ_apply]
  exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)

/-! ### `p`-chain homotopy invariance -/

/-- The `p`-null-homotopic map `∑_{i = 0}^{p - 1} e ^ i ∘ h ∘ d ^ (p - 1 - i)` associated to an
arbitrary `R`-linear operator `h : M → N`. -/
@[expose] def nullHomotopicMap (p : ℕ) (d : M →ₗ[R] M) (e : N →ₗ[R] N) (h : M →ₗ[R] N) :
    M →ₗ[R] N :=
  ∑ i ∈ Finset.range p, (e ^ i) ∘ₗ h ∘ₗ (d ^ (p - 1 - i))

/-- Pointwise evaluation of `nullHomotopicMap`. -/
theorem nullHomotopicMap_apply (p : ℕ) (d : M →ₗ[R] M) (e : N →ₗ[R] N) (h : M →ₗ[R] N)
    (m : M) :
    nullHomotopicMap p d e h m = ∑ i ∈ Finset.range p, (e ^ i) (h ((d ^ (p - 1 - i)) m)) := by
  simp [nullHomotopicMap, LinearMap.sum_apply]

/-- When `d ^ p = 0` and `e ^ p = 0`, every `nullHomotopicMap p d e h` intertwines `d` and `e`. -/
theorem nullHomotopicMap_comm {p : ℕ} {d : M →ₗ[R] M} {e : N →ₗ[R] N}
    (hd : d ^ p = 0) (he : e ^ p = 0) (h : M →ₗ[R] N) :
    nullHomotopicMap p d e h ∘ₗ d = e ∘ₗ nullHomotopicMap p d e h := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [nullHomotopicMap]
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  ext m
  simp only [LinearMap.comp_apply, nullHomotopicMap_apply, _root_.map_sum]
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  have hleft : (e ^ 0) (h ((d ^ (q + 1 - 1 - 0)) (d m))) = 0 := by
    have hpow : (d ^ q) (d m) = 0 := by
      rw [← mul_apply_eq_comp, ← pow_succ, hd, LinearMap.zero_apply]
    simp [hpow]
  have hright : e ((e ^ q) (h ((d ^ (q + 1 - 1 - q)) m))) = 0 := by
    have hpow : e ((e ^ q) (h ((d ^ (q + 1 - 1 - q)) m))) =
        (e ^ (q + 1)) (h ((d ^ (q + 1 - 1 - q)) m)) := by
      rw [pow_succ', mul_apply_eq_comp]
    rw [hpow, he, LinearMap.zero_apply]
  rw [hleft, hright, add_zero, add_zero]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  have hsub : q - i = (q - 1 - i) + 1 := by omega
  have hd_eq : (d ^ (q + 1 - 1 - (i + 1))) (d m) = (d ^ (q + 1 - 1 - i)) m := by
    simp only [Nat.add_sub_cancel]
    rw [hsub, pow_succ, mul_apply_eq_comp]
    congr 2
    omega
  rw [hd_eq, ← mul_apply_eq_comp, ← pow_succ']

/-- Every `nullHomotopicMap` carries `ker(d ^ (j + 1))` into `im(e ^ (p - j - 1))`. -/
theorem nullHomotopicMap_mem_range {p : ℕ} {d : M →ₗ[R] M} (e : N →ₗ[R] N)
    (h : M →ₗ[R] N) (j : ℕ) {z : M} (hz : z ∈ LinearMap.ker (d ^ (j + 1))) :
    nullHomotopicMap p d e h z ∈ LinearMap.range (e ^ (p - j - 1)) := by
  rw [nullHomotopicMap_apply]
  refine Submodule.sum_mem _ fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  rcases le_or_gt (p - j - 1) i with hle | hlt
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [pow_add, mul_apply_eq_comp]
    exact LinearMap.mem_range_self _ _
  · have hge : j + 1 ≤ p - 1 - i := by omega
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hge
    rw [hr, add_comm, pow_add, mul_apply_eq_comp, LinearMap.mem_ker.mp hz,
      _root_.map_zero, _root_.map_zero, _root_.map_zero]
    exact zero_mem _

/-- **A `p`-null-homotopic map induces zero on all slash homology groups.** -/
@[simp]
theorem map_nullHomotopicMap {p : ℕ} {d : M →ₗ[R] M} {e : N →ₗ[R] N}
    (hd : d ^ p = 0) (he : e ^ p = 0) (h : M →ₗ[R] N) (j : ℕ) :
    map p (nullHomotopicMap p d e h) (nullHomotopicMap_comm hd he h) j = 0 := by
  ext z
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, map_mk, LinearMap.zero_apply]
  exact (π_eq_zero_iff _).mpr (Submodule.mem_sup_left (nullHomotopicMap_mem_range e h j z.2))

/-- Two linear maps `f, g : M → N` are **`p`-homotopic** when their difference is of the form
`∑_{i = 0}^{p - 1} e ^ i ∘ h ∘ d ^ (p - 1 - i)` for some `R`-linear `h : M → N`. -/
@[expose] def IsPHomotopic (p : ℕ) (d : M →ₗ[R] M) (e : N →ₗ[R] N) (f g : M →ₗ[R] N) : Prop :=
  ∃ h : M →ₗ[R] N, f - g = nullHomotopicMap p d e h

/-- `IsPHomotopic` is reflexive. -/
@[refl]
theorem IsPHomotopic.refl (p : ℕ) (d : M →ₗ[R] M) (e : N →ₗ[R] N) (f : M →ₗ[R] N) :
    IsPHomotopic p d e f f :=
  ⟨0, by simp [nullHomotopicMap]⟩

/-- `IsPHomotopic` is symmetric. -/
@[symm]
theorem IsPHomotopic.symm {p : ℕ} {d : M →ₗ[R] M} {e : N →ₗ[R] N} {f g : M →ₗ[R] N}
    (hfg : IsPHomotopic p d e f g) : IsPHomotopic p d e g f := by
  obtain ⟨h, hh⟩ := hfg
  refine ⟨-h, ?_⟩
  rw [← neg_sub, hh]
  simp [nullHomotopicMap, LinearMap.comp_neg, LinearMap.neg_comp]

/-- `IsPHomotopic` is transitive. -/
@[trans]
theorem IsPHomotopic.trans {p : ℕ} {d : M →ₗ[R] M} {e : N →ₗ[R] N} {f g k : M →ₗ[R] N}
    (hfg : IsPHomotopic p d e f g) (hgk : IsPHomotopic p d e g k) :
    IsPHomotopic p d e f k := by
  obtain ⟨h₁, hh₁⟩ := hfg
  obtain ⟨h₂, hh₂⟩ := hgk
  refine ⟨h₁ + h₂, ?_⟩
  rw [← sub_add_sub_cancel f g k, hh₁, hh₂]
  simp [nullHomotopicMap, LinearMap.comp_add, LinearMap.add_comp, Finset.sum_add_distrib]

/-- **Homotopy invariance of slash homology.** Two `p`-homotopic intertwining maps between
`p`-differentials induce the same map on every slash homology group. -/
theorem map_eq_of_isPHomotopic {p : ℕ} {d : M →ₗ[R] M} {e : N →ₗ[R] N}
    (hd : d ^ p = 0) (he : e ^ p = 0) {f g : M →ₗ[R] N}
    (hf : f ∘ₗ d = e ∘ₗ f) (hg : g ∘ₗ d = e ∘ₗ g)
    (hfg : IsPHomotopic p d e f g) (j : ℕ) :
    map p f hf j = map p g hg j := by
  obtain ⟨h, hh⟩ := hfg
  rw [← sub_eq_zero, ← map_sub p f g hf hg j]
  have hcongr :
      map p (f - g) (by rw [LinearMap.sub_comp, LinearMap.comp_sub, hf, hg]) j =
        map p (nullHomotopicMap p d e h) (nullHomotopicMap_comm hd he h) j := by
    congr! 1
  rw [hcongr, map_nullHomotopicMap hd he h j]

/-- On a nonzero module with zero differential, the identity map is never `p`-null-homotopic for
`2 ≤ p`: every summand `0 ^ i ∘ h ∘ 0 ^ (p - 1 - i)` has a positive exponent on `0`. -/
theorem not_isPHomotopic_id_zero_of_two_le [Nontrivial M] {p : ℕ} (hp : 2 ≤ p) :
    ¬ IsPHomotopic p (0 : M →ₗ[R] M) (0 : M →ₗ[R] M) LinearMap.id 0 := by
  rintro ⟨h, hh⟩
  have hzero : nullHomotopicMap p (0 : M →ₗ[R] M) (0 : M →ₗ[R] M) h = 0 := by
    unfold nullHomotopicMap
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have hpos : p - 1 ≠ 0 := by omega
      simp [zero_pow hpos]
    · simp [zero_pow hi0.ne']
  rw [sub_zero, hzero] at hh
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  exact hx (by simpa using LinearMap.congr_fun hh x)

/-! ### Characterization of vanishing slash homology -/

/-- **Exact-filtration criterion.** When `d ^ p = 0`, all slash homology groups
`SlashHomology p d j` for `j + 1 < p` vanish if and only if `ker(d ^ m) = im(d ^ (p - m))` for
every `m ≤ p`. -/
theorem forall_subsingleton_iff_ker_pow_eq_range_pow {p : ℕ} {d : M →ₗ[R] M} (hd : d ^ p = 0) :
    (∀ j, j + 1 < p → Subsingleton (SlashHomology p d j)) ↔
      ∀ m ≤ p, LinearMap.ker (d ^ m) = LinearMap.range (d ^ (p - m)) := by
  constructor
  · intro h m hm
    induction m with
    | zero =>
      simp [Module.End.one_eq_id, hd]
    | succ j ih =>
      rcases eq_or_lt_of_le hm with rfl | hlt
      · simp [hd, Module.End.one_eq_id]
      · have ihj := ih (by omega)
        have hle_range : LinearMap.range (d ^ (p - j)) ≤ LinearMap.range (d ^ (p - j - 1)) := by
          rintro _ ⟨x, rfl⟩
          have hsub : p - j = (p - j - 1) + 1 := by omega
          rw [hsub, pow_succ, mul_apply_eq_comp]
          exact LinearMap.mem_range_self _ _
        have hj := (subsingleton_iff_ker_eq hd j).mp (h j hlt)
        rw [hj, ihj, sup_of_le_left hle_range, Nat.sub_sub]
  · intro h j hj
    rw [subsingleton_iff, h (j + 1) (by omega), Nat.sub_sub]
    exact le_sup_left

/-- Reformulation with `j ≤ p - 2` when `d ^ p = 0` and `2 ≤ p`: all `SlashHomology p d j` for
`j ≤ p - 2` vanish iff `ker(d ^ m) = im(d ^ (p - m))` for every `m ≤ p`. -/
theorem forall_le_sub_two_subsingleton_iff_ker_pow_eq_range_pow {p : ℕ} {d : M →ₗ[R] M}
    (hp : 2 ≤ p) (hd : d ^ p = 0) :
    (∀ j ≤ p - 2, Subsingleton (SlashHomology p d j)) ↔
      ∀ m ≤ p, LinearMap.ker (d ^ m) = LinearMap.range (d ^ (p - m)) := by
  rw [← forall_subsingleton_iff_ker_pow_eq_range_pow hd]
  exact ⟨fun h j hj ↦ h j (by omega), fun h j hj ↦ h j (by omega)⟩

end SlashHomology

end Ring

/-! ### Monomial bases and Khovanov–Qi's dimension decomposition over a field -/

namespace SlashHomology

section Field

universe v

variable {k : Type*} {M : Type v} [Field k] [AddCommGroup M] [Module k M]

private theorem top_le_iSup_map_pow_of_isCompl {d : M →ₗ[k] M} {W : Submodule k M}
    (hW : IsCompl (LinearMap.range d) W) {p : ℕ} (hd : d ^ p = 0) :
    (⊤ : Submodule k M) ≤ ⨆ r : Fin p, W.map (d ^ (r : ℕ)) := by
  -- Iterating `M = im d ⊔ W` gives `M ≤ (⨆_{r < m} d^r W) ⊔ im(d^m)` for every `m ≤ p`.
  have hstep : ∀ m ≤ p,
      (⊤ : Submodule k M) ≤
        (⨆ (r : Fin p) (_ : (r : ℕ) < m), W.map (d ^ (r : ℕ))) ⊔ LinearMap.range (d ^ m) := by
    intro m hm
    induction m with
    | zero =>
      simp [Module.End.one_eq_id]
    | succ m ih =>
      refine (ih (by omega)).trans (sup_le ?_ ?_)
      · exact le_sup_of_le_left <| iSup₂_mono' fun r hr ↦ ⟨r, by omega, le_rfl⟩
      · rintro _ ⟨x, rfl⟩
        have hx : x ∈ LinearMap.range d ⊔ W := hW.codisjoint.eq_top ▸ Submodule.mem_top
        rcases Submodule.mem_sup.mp hx with ⟨u, ⟨y, rfl⟩, w, hw, rfl⟩
        rw [_root_.map_add]
        refine add_mem ?_ ?_
        · exact Submodule.mem_sup_right ⟨y, by rw [pow_succ, mul_apply_eq_comp]⟩
        · refine Submodule.mem_sup_left ?_
          exact (le_iSup₂ (f := fun (r : Fin p) (_ : (r : ℕ) < m + 1) ↦ W.map (d ^ (r : ℕ)))
            ⟨m, hm⟩ (lt_add_one m)) ⟨w, hw, rfl⟩
  simpa [hd] using hstep p le_rfl

private theorem eq_zero_of_sum_pow_eq_zero {d : M →ₗ[k] M} {W : Submodule k M}
    (hW : IsCompl (LinearMap.range d) W) {p : ℕ} (hd : d ^ p = 0)
    (hker : LinearMap.ker (d ^ (p - 1)) ≤ LinearMap.range d)
    {w : Fin p → W} (hsum : ∑ r : Fin p, (d ^ (r : ℕ)) (w r : M) = 0) :
    ∀ n (hn : n < p), w ⟨n, hn⟩ = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro hn
    have happ := congrArg (d ^ (p - 1 - n)) hsum
    rw [_root_.map_zero, _root_.map_sum] at happ
    have hsub_add : p - 1 - n + n = p - 1 := by omega
    have hsingle :
        ∑ r : Fin p, (d ^ (p - 1 - n)) ((d ^ (r : ℕ)) (w r : M)) =
          (d ^ (p - 1)) (w ⟨n, hn⟩ : M) := by
      rw [Finset.sum_eq_single ⟨n, hn⟩]
      · rw [← mul_apply_eq_comp, ← pow_add, hsub_add]
      · intro r _ hrne
        rcases lt_trichotomy (r : ℕ) n with hlt | heq | hgt
        · simp [ih r hlt r.2]
        · exact absurd (Fin.ext heq) hrne
        · rw [← mul_apply_eq_comp, ← pow_add,
            pow_eq_zero_of_le (by omega : p ≤ p - 1 - n + r) hd, LinearMap.zero_apply]
      · simp [Finset.mem_univ]
    rw [hsingle] at happ
    have hmem : (w ⟨n, hn⟩ : M) ∈ LinearMap.range d ⊓ W :=
      ⟨hker (LinearMap.mem_ker.mpr happ), (w ⟨n, hn⟩).2⟩
    rw [hW.disjoint.eq_bot, Submodule.mem_bot] at hmem
    exact Subtype.ext hmem

private theorem linearIndependent_pow_basis_of_isCompl {d : M →ₗ[k] M} {W : Submodule k M}
    (hW : IsCompl (LinearMap.range d) W) {p : ℕ} (hd : d ^ p = 0)
    (hker : LinearMap.ker (d ^ (p - 1)) ≤ LinearMap.range d)
    {ι : Type*} (b : Module.Basis ι k W) :
    LinearIndependent k (fun ir : ι × Fin p ↦ (d ^ (ir.2 : ℕ)) (b ir.1)) := by
  classical
  rw [linearIndependent_iff']
  intro s c hc ir hir
  -- Group the linear relation by powers `r : Fin p` into vectors `w r ∈ W`.
  let w : Fin p → W := fun r ↦
    ∑ i ∈ s.image Prod.fst, (if (i, r) ∈ s then c (i, r) else 0) • b i
  have hsum : ∑ r : Fin p, (d ^ (r : ℕ)) (w r : M) = 0 := by
    have h1 : ∑ r : Fin p, (d ^ (r : ℕ)) (w r : M) =
        ∑ i ∈ s.image Prod.fst, ∑ r : Fin p,
          (if (i, r) ∈ s then c (i, r) • (d ^ (r : ℕ)) (b i) else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      simp only [w, Submodule.coe_sum, Submodule.coe_smul_of_tower, _root_.map_sum, map_smul]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      split_ifs <;> simp
    rw [h1, ← Finset.sum_product']
    have hsub : s ⊆ (s.image Prod.fst) ×ˢ Finset.univ := fun x hx ↦
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx, Finset.mem_univ _⟩
    rw [← Finset.sum_subset hsub (fun _ _ hx ↦ by simp [hx])]
    simpa using hc
  have hwir := eq_zero_of_sum_pow_eq_zero hW hd hker hsum ir.2 ir.2.2
  have hlin := linearIndependent_iff'.mp b.linearIndependent (s.image Prod.fst)
    (fun i ↦ if (i, ir.2) ∈ s then c (i, ir.2) else 0) hwir ir.1
    (Finset.mem_image_of_mem Prod.fst hir)
  simpa [hir] using hlin

/-- **Monomial `k`-basis from vanishing slash homology.** Over a field `k` (without assuming finite
dimensionality), if `d : M →ₗ[k] M` satisfies `d ^ p = 0` and all `SlashHomology p d j` for
`j + 1 < p` vanish, then choosing any complement of `im d` yields an indexed family `v : ι → M`
for which `(i, r) ↦ (d ^ r) (v i)` is a `k`-basis of `M`. -/
theorem exists_basis_pow_of_forall_subsingleton {p : ℕ} {d : M →ₗ[k] M}
    (hd : d ^ p = 0)
    (hsub : ∀ j, j + 1 < p → Subsingleton (SlashHomology p d j)) :
    ∃ (ι : Type v) (v : ι → M) (b : Module.Basis (ι × Fin p) k M),
      ∀ (i : ι) (r : Fin p), b (i, r) = (d ^ (r : ℕ)) (v i) := by
  obtain ⟨W, hW⟩ := (LinearMap.range d).exists_isCompl
  obtain ⟨ι, ⟨bW⟩⟩ : ∃ (ι : Type v), Nonempty (Module.Basis ι k W) :=
    ⟨Module.Basis.ofVectorSpaceIndex k W, ⟨Module.Basis.ofVectorSpace k W⟩⟩
  have hker_all := (forall_subsingleton_iff_ker_pow_eq_range_pow hd).mp hsub
  have hker : LinearMap.ker (d ^ (p - 1)) ≤ LinearMap.range d := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · intro x _
      rw [pow_zero, Module.End.one_eq_id] at hd
      have hx : x = 0 := by simpa using LinearMap.congr_fun hd x
      simp [hx]
    · have h1 := hker_all (p - 1) (by omega)
      have hsub1 : p - (p - 1) = 1 := by omega
      rw [hsub1, pow_one] at h1
      exact h1.le
  have hli := linearIndependent_pow_basis_of_isCompl hW hd hker bW
  have hspan : (⊤ : Submodule k M) ≤
      Submodule.span k (Set.range fun ir : ι × Fin p ↦ (d ^ (ir.2 : ℕ)) (bW ir.1 : M)) := by
    refine (top_le_iSup_map_pow_of_isCompl hW hd).trans (iSup_le fun r ↦ ?_)
    rintro _ ⟨w, hw, rfl⟩
    have happ := congrArg (fun x : W ↦ (d ^ (r : ℕ)) (x : M)) (bW.linearCombination_repr ⟨w, hw⟩)
    dsimp only at happ
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum, _root_.map_sum] at happ
    rw [← happ]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [Submodule.coe_smul_of_tower, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, r), rfl⟩)
  refine ⟨ι, fun i ↦ (bW i : M), Module.Basis.mk hli hspan, fun i r ↦ ?_⟩
  simp [Module.Basis.mk_apply]

/-! ### Dimension formulas for finite-dimensional `p`-complexes -/

/-- For a finite-dimensional `p`-complex (`d ^ p = 0`) and `j + 1 < p`,
`dim H^{/j}(M) + dim ker(d ^ j) + dim im(d ^ (p - 1)) = dim ker(d ^ (j + 1))`. -/
theorem finrank_add_finrank_ker_add_finrank_range [FiniteDimensional k M]
    {p : ℕ} {d : M →ₗ[k] M} (hd : d ^ p = 0) {j : ℕ} (hj : j + 1 < p) :
    Module.finrank k (SlashHomology p d j) +
        Module.finrank k (LinearMap.ker (d ^ j)) +
        Module.finrank k (LinearMap.range (d ^ (p - 1))) =
      Module.finrank k (LinearMap.ker (d ^ (j + 1))) := by
  let S := LinearMap.range (d ^ (p - j - 1))
  let K := LinearMap.ker (d ^ j)
  let C := LinearMap.ker (d ^ (j + 1))
  have hle : S ⊔ K ≤ C := range_sup_ker_le_ker hd j
  -- Under `C.subtype`, the comap submodule `boundaries p d j` maps isomorphically onto `S ⊔ K`.
  have hmap : (boundaries p d j).map C.subtype = S ⊔ K := by
    rw [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.mpr hle]
  have hbd : Module.finrank k (boundaries p d j) = Module.finrank k ↥(S ⊔ K) := by
    rw [← hmap]
    exact (Submodule.equivMapOfInjective C.subtype C.injective_subtype _).finrank_eq
  -- Restrict `d ^ j` to `S = im(d ^ (p - j - 1))`; its range is `im(d ^ (p - 1))` and its kernel
  -- is isomorphic to `S ⊓ K`.
  let f : S →ₗ[k] M := (d ^ j).domRestrict S
  have hj_add : j + (p - j - 1) = p - 1 := by omega
  have hfrange : LinearMap.range f = LinearMap.range (d ^ (p - 1)) := by
    ext y
    simp only [f, LinearMap.mem_range, LinearMap.domRestrict_apply, S]
    constructor
    · rintro ⟨⟨_, ⟨x, rfl⟩⟩, rfl⟩
      exact ⟨x, by rw [← mul_apply_eq_comp, ← pow_add, hj_add]⟩
    · rintro ⟨x, rfl⟩
      refine ⟨⟨(d ^ (p - j - 1)) x, LinearMap.mem_range_self _ x⟩, ?_⟩
      rw [← mul_apply_eq_comp, ← pow_add, hj_add]
  have hfker : Module.finrank k (LinearMap.ker f) = Module.finrank k ↥(S ⊓ K) := by
    have hkeq : (LinearMap.ker f).map S.subtype = S ⊓ K := by
      ext x
      simp only [Submodule.mem_map, LinearMap.mem_ker, f, LinearMap.domRestrict_apply,
        Submodule.coe_subtype, Submodule.mem_inf, K]
      exact ⟨fun ⟨u, hu, hux⟩ ↦ ⟨hux ▸ u.2, hux ▸ hu⟩, fun ⟨hxS, hxK⟩ ↦ ⟨⟨x, hxS⟩, hxK, rfl⟩⟩
    rw [← hkeq]
    exact (Submodule.equivMapOfInjective S.subtype S.injective_subtype _).finrank_eq
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hfrange, hfker] at hrn
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq S K
  have hquot :
      Module.finrank k (SlashHomology p d j) + Module.finrank k (boundaries p d j) =
        Module.finrank k (LinearMap.ker (d ^ (j + 1))) :=
    (boundaries p d j).finrank_quotient_add_finrank
  rw [hbd] at hquot
  dsimp only [S, K] at hrn hmod hquot
  omega

/-- **Khovanov–Qi's dimension decomposition** (arXiv:1208.0616, §2, equation (20)). For any
finite-dimensional vector space `M` over `k` and endomorphism `d : M →ₗ[k] M` with `d ^ p = 0`
(`0 < p`),
`finrank k M = p * finrank k (range (d ^ (p - 1))) + ∑_{j = 0}^{p - 2} finrank k H^{/j}(M)`. -/
theorem finrank_eq_mul_finrank_range_pow_add_sum [FiniteDimensional k M]
    {p : ℕ} {d : M →ₗ[k] M} (hp : 0 < p) (hd : d ^ p = 0) :
    Module.finrank k M =
      p * Module.finrank k (LinearMap.range (d ^ (p - 1))) +
        ∑ j ∈ Finset.range (p - 1), Module.finrank k (SlashHomology p d j) := by
  -- Sum the telescoping identity `finrank_add_finrank_ker_add_finrank_range` over `0 ≤ j < p - 1`.
  have htel : ∀ m ≤ p - 1,
      Module.finrank k (LinearMap.ker (d ^ m)) =
        m * Module.finrank k (LinearMap.range (d ^ (p - 1))) +
          ∑ j ∈ Finset.range m, Module.finrank k (SlashHomology p d j) := by
    intro m hm
    induction m with
    | zero =>
      simp [Module.End.one_eq_id]
    | succ m ih =>
      rw [Finset.sum_range_succ, ← finrank_add_finrank_ker_add_finrank_range hd (by omega),
        ih (by omega), Nat.succ_mul]
      omega
  have hp1 := htel (p - 1) le_rfl
  have hrn := LinearMap.finrank_range_add_finrank_ker (d ^ (p - 1))
  have hadd : 1 + (p - 1) = p := by omega
  have hmul :
      Module.finrank k (LinearMap.range (d ^ (p - 1))) +
          (p - 1) * Module.finrank k (LinearMap.range (d ^ (p - 1))) =
        p * Module.finrank k (LinearMap.range (d ^ (p - 1))) := by
    simpa [one_mul, add_comm] using
      (Nat.add_mul 1 (p - 1) (Module.finrank k (LinearMap.range (d ^ (p - 1))))).symm.trans
        (by rw [hadd])
  omega

end Field

end SlashHomology

end TauCeti
