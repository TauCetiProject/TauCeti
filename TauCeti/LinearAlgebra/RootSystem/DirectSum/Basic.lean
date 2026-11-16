/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import TauCeti.LinearAlgebra.PerfectPairing.Pi
public import TauCeti.LinearAlgebra.RootSystem.Chamber
public import TauCeti.LinearAlgebra.RootSystem.Dominance
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group
import Mathlib.Algebra.Ring.Regular
import TauCeti.Algebra.Group.Submonoid.Closure
import TauCeti.LinearAlgebra.Pi

/-!
# Finite external direct sums of root pairings

Given a finite family of root pairings `P c : RootPairing (ι c) R (M c) (N c)` over a commutative
ring `R` with `2 ≠ 0`, their external direct sum `RootPairing.pi P` is the root pairing indexed by
the disjoint union `Σ c, ι c` on the product modules `∀ c, M c` and `∀ c, N c`. The pairing between
the products is `LinearMap.piPairing`, which is perfect by `LinearMap.IsPerfPair.pi`, and the roots
and coroots of the `c`-th summand sit in the `c`-th coordinate via `Pi.single`.

The hypothesis `NeZero (2 : R)` is required so that each summand's roots and coroots are nonzero
(`RootPairing.ne_zero`, `RootPairing.ne_zero'`), keeping the coordinate injections disjoint across
distinct summands. Roots from distinct summands are orthogonal, so the reflection at `⟨c, i⟩` acts
as `(P c).reflection i` on coordinate `c` and fixes all other coordinates; in particular, the set
of roots is the union of the coordinate images of the summands' roots, with no cross-summand sums.

The construction preserves root systems (`IsRootSystem`), subring-valuedness (`IsValuedIn`, hence
`IsCrystallographic`), reducedness (when `2` is regular, in particular when `R` has no zero
divisors), and anisotropy (`IsAnisotropic`). Bases assemble componentwise into
`RootPairing.Base.pi`, whose Cartan matrix is block diagonal, and whose heights, positive roots,
positive root cone, integral root dominance, regular weights, and closed and open dominant chambers
all decompose coordinatewise. The canonical bilinear form `RootForm` is the orthogonal sum of the
summands' forms, and the Weyl group is canonically isomorphic to the product of the summands' Weyl
groups.

## Main definitions

* `RootPairing.pi`: the finite external direct sum of a family of root pairings.
* `RootPairing.Base.pi`: the base of `RootPairing.pi P` assembled from a base of each summand.
* `RootPairing.Equiv.piCongr`: functoriality of `RootPairing.pi` under reindexing and summand
  equivalences.
* `RootPairing.piAut`: the canonical embedding of `∀ c, (P c).Aut` into `(RootPairing.pi P).Aut`.
* `RootPairing.piWeylGroupEquiv`: the canonical group isomorphism
  `(RootPairing.pi P).weylGroup ≃* ∀ c, (P c).weylGroup`.

## Main results

* `RootPairing.range_pi_root`: the roots of `RootPairing.pi P` are the union of the coordinate
  images of the summands' roots.
* `RootPairing.isRootSystem_pi`, `RootPairing.isValuedIn_pi`, `RootPairing.isReduced_pi`,
  `RootPairing.isAnisotropic_pi`: structural instances preserved by finite direct sums.
* `RootPairing.pi_rootForm_apply_apply`: the canonical bilinear form splits as the orthogonal sum
  of the summands' root forms.
* `RootPairing.Base.height_pi`, `RootPairing.Base.isPos_pi_iff`,
  `RootPairing.mem_posRootCone_pi_iff`, `RootPairing.rootLE_pi_iff`,
  `RootPairing.mem_dominantChamber_pi_iff`, `RootPairing.mem_openDominantChamber_pi_iff`:
  coordinatewise decomposition of heights, positive roots, cones, dominance, and chambers.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §1, no. 2.
* J. S. Milne, *Algebraic Groups*, Cambridge University Press (2017), Appendix C, C.23.
-/

public section

open Function Set Submodule

namespace RootPairing

section Basic

variable {κ R : Type*} [Fintype κ] [DecidableEq κ] [CommRing R] [NeZero (2 : R)]
  {ι M N : κ → Type*}
  [∀ c, AddCommGroup (M c)] [∀ c, Module R (M c)]
  [∀ c, AddCommGroup (N c)] [∀ c, Module R (N c)]
  (P : ∀ c, RootPairing (ι c) R (M c) (N c))

omit [Fintype κ] [NeZero (2 : R)] in
/-- The coordinatewise reflection permutation on `Σ c, ι c`: reflection in `⟨c, i⟩` acts on the
`c`-th summand by `(P c).reflectionPerm i` and fixes all other summands. -/
private noncomputable def piReflectionPerm (s : Σ c, ι c) : _root_.Equiv.Perm (Σ c, ι c) :=
  _root_.Equiv.sigmaCongrRight fun d ↦
    if h : d = s.1 then (P d).reflectionPerm (h ▸ s.2) else _root_.Equiv.refl (ι d)

omit [Fintype κ] [NeZero (2 : R)] in
private theorem piReflectionPerm_same (c : κ) (i j : ι c) :
    piReflectionPerm P ⟨c, i⟩ ⟨c, j⟩ = ⟨c, (P c).reflectionPerm i j⟩ := by
  simp [piReflectionPerm]

omit [Fintype κ] [NeZero (2 : R)] in
private theorem piReflectionPerm_ne {c d : κ} (hcd : c ≠ d) (i : ι c) (j : ι d) :
    piReflectionPerm P ⟨c, i⟩ ⟨d, j⟩ = ⟨d, j⟩ := by
  simp [piReflectionPerm, Ne.symm hcd]

omit [Fintype κ] in
private theorem pi_root_injective :
    Function.Injective fun s : Σ c, ι c ↦ Pi.single s.1 ((P s.1).root s.2) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ h
  by_cases hcd : c = d
  · subst hcd
    have hi : (P c).root i = (P c).root j := by simpa using congrFun h c
    exact congrArg (Sigma.mk c) ((P c).root.injective hi)
  · have h0 : (P c).root i = 0 := by simpa [Pi.single_eq_of_ne hcd] using congrFun h c
    exact ((P c).ne_zero i h0).elim

omit [Fintype κ] in
private theorem pi_coroot_injective :
    Function.Injective fun s : Σ c, ι c ↦ Pi.single s.1 ((P s.1).coroot s.2) :=
  pi_root_injective fun c ↦ (P c).flip

/-- **The finite external direct sum of a family of root pairings.**

The weight and coweight spaces are `∀ c, M c` and `∀ c, N c`, paired by `LinearMap.piPairing`,
and the roots and coroots of each summand `P c` sit in the `c`-th coordinate via `Pi.single`. -/
noncomputable def pi : RootPairing (Σ c, ι c) R (∀ c, M c) (∀ c, N c) where
  toLinearMap := LinearMap.piPairing fun c ↦ (P c).toLinearMap
  root := ⟨fun s ↦ Pi.single s.1 ((P s.1).root s.2), pi_root_injective P⟩
  coroot := ⟨fun s ↦ Pi.single s.1 ((P s.1).coroot s.2), pi_coroot_injective P⟩
  root_coroot_two s := by
    simp only [Function.Embedding.coeFn_mk, LinearMap.piPairing_single_left, Pi.single_eq_same,
      root_coroot_two]
  reflectionPerm := piReflectionPerm P
  reflectionPerm_root := by
    rintro ⟨c, i⟩ ⟨d, j⟩
    simp only [Function.Embedding.coeFn_mk]
    by_cases hcd : c = d
    · subst hcd
      rw [piReflectionPerm_same]
      ext e
      by_cases he : e = c
      · subst he
        simp [reflection_apply]
      · simp [Pi.single_eq_of_ne he]
    · rw [piReflectionPerm_ne P hcd]
      simp [Pi.single_eq_of_ne hcd]
  reflectionPerm_coroot := by
    rintro ⟨c, i⟩ ⟨d, j⟩
    simp only [Function.Embedding.coeFn_mk]
    by_cases hcd : c = d
    · subst hcd
      rw [piReflectionPerm_same]
      ext e
      by_cases he : e = c
      · subst he
        simp [coreflection_apply, root', root_coroot_eq_pairing]
      · simp [Pi.single_eq_of_ne he]
    · rw [piReflectionPerm_ne P hcd]
      simp [Pi.single_eq_of_ne (Ne.symm hcd)]

@[simp]
theorem pi_toLinearMap :
    (pi P).toLinearMap = LinearMap.piPairing fun c ↦ (P c).toLinearMap :=
  (rfl)

theorem pi_toLinearMap_apply (x : ∀ c, M c) (y : ∀ c, N c) :
    (pi P).toLinearMap x y = ∑ c, (P c).toLinearMap (x c) (y c) :=
  LinearMap.piPairing_apply_apply _ x y

@[simp]
theorem pi_root (c : κ) (i : ι c) :
    (pi P).root ⟨c, i⟩ = Pi.single c ((P c).root i) :=
  (rfl)

@[simp]
theorem pi_coroot (c : κ) (i : ι c) :
    (pi P).coroot ⟨c, i⟩ = Pi.single c ((P c).coroot i) :=
  (rfl)

theorem pi_coroot'_apply (c : κ) (i : ι c) (x : ∀ d, M d) :
    (pi P).coroot' ⟨c, i⟩ x = (P c).coroot' i (x c) := by
  simp [coroot', pi_toLinearMap, pi_coroot]

theorem pi_root'_apply (c : κ) (i : ι c) (y : ∀ d, N d) :
    (pi P).root' ⟨c, i⟩ y = (P c).root' i (y c) := by
  simp [root', pi_toLinearMap, pi_root]

@[simp]
theorem pi_pairing_same (c : κ) (i j : ι c) :
    (pi P).pairing ⟨c, i⟩ ⟨c, j⟩ = (P c).pairing i j := by
  rw [← root_coroot_eq_pairing, ← root_coroot_eq_pairing, pi_toLinearMap, pi_root, pi_coroot,
    LinearMap.piPairing_single_left, Pi.single_eq_same]

@[simp]
theorem pi_pairing_ne {c d : κ} (hcd : c ≠ d) (i : ι c) (j : ι d) :
    (pi P).pairing ⟨c, i⟩ ⟨d, j⟩ = 0 := by
  rw [← root_coroot_eq_pairing, pi_toLinearMap, pi_root, pi_coroot,
    LinearMap.piPairing_single_left, Pi.single_eq_of_ne hcd, map_zero]

/-- Roots in distinct summands of a finite direct sum are orthogonal. -/
theorem isOrthogonal_pi_of_ne {c d : κ} (hcd : c ≠ d) (i : ι c) (j : ι d) :
    (pi P).IsOrthogonal ⟨c, i⟩ ⟨d, j⟩ :=
  ⟨pi_pairing_ne P hcd i j, pi_pairing_ne P hcd.symm j i⟩

@[simp]
theorem pi_reflectionPerm_same (c : κ) (i j : ι c) :
    (pi P).reflectionPerm ⟨c, i⟩ ⟨c, j⟩ = ⟨c, (P c).reflectionPerm i j⟩ :=
  piReflectionPerm_same P c i j

@[simp]
theorem pi_reflectionPerm_ne {c d : κ} (hcd : c ≠ d) (i : ι c) (j : ι d) :
    (pi P).reflectionPerm ⟨c, i⟩ ⟨d, j⟩ = ⟨d, j⟩ :=
  piReflectionPerm_ne P hcd i j

@[simp]
theorem pi_reflection_apply_same (c : κ) (i : ι c) (x : ∀ d, M d) :
    (pi P).reflection ⟨c, i⟩ x c = (P c).reflection i (x c) := by
  simp [reflection_apply]

@[simp]
theorem pi_reflection_apply_ne {c d : κ} (hdc : d ≠ c) (i : ι c) (x : ∀ e, M e) :
    (pi P).reflection ⟨c, i⟩ x d = x d := by
  simp [reflection_apply, Pi.single_eq_of_ne hdc]

@[simp]
theorem pi_coreflection_apply_same (c : κ) (i : ι c) (y : ∀ d, N d) :
    (pi P).coreflection ⟨c, i⟩ y c = (P c).coreflection i (y c) := by
  simp [coreflection_apply, pi_root'_apply]

@[simp]
theorem pi_coreflection_apply_ne {c d : κ} (hdc : d ≠ c) (i : ι c) (y : ∀ e, N e) :
    (pi P).coreflection ⟨c, i⟩ y d = y d := by
  simp [coreflection_apply, Pi.single_eq_of_ne hdc]

/-- **The roots of a finite direct sum are the union of the coordinate images of the summands'
roots.** In particular, no sum of nonzero roots from distinct summands is a root. -/
theorem range_pi_root :
    range (pi P).root = ⋃ c, Pi.single c '' range (P c).root := by
  ext x
  simp only [mem_range, mem_iUnion, mem_image, Sigma.exists]
  constructor
  · rintro ⟨c, i, rfl⟩
    exact ⟨c, (P c).root i, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨c, _, ⟨i, rfl⟩, rfl⟩
    exact ⟨c, i, rfl⟩

/-- The coroots of a finite direct sum are the union of the coordinate images of the summands'
coroots. -/
theorem range_pi_coroot :
    range (pi P).coroot = ⋃ c, Pi.single c '' range (P c).coroot := by
  ext y
  simp only [mem_range, mem_iUnion, mem_image, Sigma.exists]
  constructor
  · rintro ⟨c, i, rfl⟩
    exact ⟨c, (P c).coroot i, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨c, _, ⟨i, rfl⟩, rfl⟩
    exact ⟨c, i, rfl⟩

/-- Flipping a finite direct sum of root pairings gives the finite direct sum of the flipped
pairings. -/
theorem pi_flip : (pi P).flip = pi fun c ↦ (P c).flip := by
  have hext : ∀ {A B : RootPairing (Σ c, ι c) R (∀ c, N c) (∀ c, M c)},
      A.toLinearMap = B.toLinearMap → A.root = B.root → A.coroot = B.coroot →
        A.reflectionPerm = B.reflectionPerm → A = B := by
    intro A B h1 h2 h3 h4
    cases A
    cases B
    simp only at h1 h2 h3 h4
    subst h1 h2 h3 h4
    rfl
  exact hext (LinearMap.flip_piPairing _) rfl rfl rfl

/-! ### Structural properties -/

/-- The `S`-span of the roots of a finite direct sum is the coordinatewise product of the
summands' root spans. -/
theorem mem_rootSpan_pi_iff (S : Type*) [Semiring S] [∀ c, Module S (M c)] (x : ∀ c, M c) :
    x ∈ span S (range (pi P).root) ↔ ∀ c, x c ∈ span S (range (P c).root) := by
  constructor
  · intro hx c
    have hmap : LinearMap.proj (R := S) (φ := M) c x ∈
        (span S (range (pi P).root)).map (LinearMap.proj (R := S) (φ := M) c) :=
      mem_map_of_mem hx
    rw [Submodule.map_span] at hmap
    refine (span_le.mpr ?_) hmap
    rintro _ ⟨_, ⟨⟨d, i⟩, rfl⟩, rfl⟩
    by_cases hdc : d = c
    · subst hdc
      exact subset_span ⟨i, by simp⟩
    · simp [Pi.single_eq_of_ne (Ne.symm hdc)]
  · intro hx
    rw [← Finset.univ_sum_single x]
    refine sum_mem fun c _ ↦ ?_
    have hmem : LinearMap.single S M c (x c) ∈
        (span S (range (P c).root)).map (LinearMap.single S M c) :=
      mem_map_of_mem (hx c)
    rw [Submodule.map_span] at hmem
    refine span_mono ?_ hmem
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨⟨c, i⟩, rfl⟩

/-- The `S`-span of the coroots of a finite direct sum is the coordinatewise product of the
summands' coroot spans. -/
theorem mem_corootSpan_pi_iff (S : Type*) [Semiring S] [∀ c, Module S (N c)] (y : ∀ c, N c) :
    y ∈ span S (range (pi P).coroot) ↔ ∀ c, y c ∈ span S (range (P c).coroot) := by
  have h := mem_rootSpan_pi_iff (fun c ↦ (P c).flip) S y
  rwa [← pi_flip] at h

/-- **A finite direct sum of root systems is a root system.** -/
instance isRootSystem_pi [∀ c, (P c).IsRootSystem] : (pi P).IsRootSystem where
  span_root_eq_top := eq_top_iff.mpr fun x _ ↦ (mem_rootSpan_pi_iff P R x).mpr fun c ↦ by
    rw [IsRootSystem.span_root_eq_top]
    exact mem_top
  span_coroot_eq_top := eq_top_iff.mpr fun y _ ↦ (mem_corootSpan_pi_iff P R y).mpr fun c ↦ by
    rw [IsRootSystem.span_coroot_eq_top]
    exact mem_top

/-- **A finite direct sum of `S`-valued root pairings is `S`-valued.** In particular, a finite
direct sum of crystallographic root pairings is crystallographic. -/
instance isValuedIn_pi (S : Type*) [CommRing S] [Algebra S R] [∀ c, (P c).IsValuedIn S] :
    (pi P).IsValuedIn S where
  exists_value := by
    rintro ⟨c, i⟩ ⟨d, j⟩
    by_cases hcd : c = d
    · subst hcd
      simpa using (P c).exists_value (S := S) i j
    · exact ⟨0, by simp [pi_pairing_ne P hcd]⟩

@[simp]
theorem pi_pairingIn_same (S : Type*) [CommRing S] [Algebra S R] [FaithfulSMul S R]
    [∀ c, (P c).IsValuedIn S] (c : κ) (i j : ι c) :
    (pi P).pairingIn S ⟨c, i⟩ ⟨c, j⟩ = (P c).pairingIn S i j :=
  FaithfulSMul.algebraMap_injective S R <| by simp

@[simp]
theorem pi_pairingIn_ne (S : Type*) [CommRing S] [Algebra S R] [FaithfulSMul S R]
    [∀ c, (P c).IsValuedIn S] {c d : κ} (hcd : c ≠ d) (i : ι c) (j : ι d) :
    (pi P).pairingIn S ⟨c, i⟩ ⟨d, j⟩ = 0 :=
  FaithfulSMul.algebraMap_injective S R <| by simp [pi_pairing_ne P hcd]

/-- **A finite direct sum of reduced root pairings is reduced**, provided `2` is regular in `R`. -/
theorem isReduced_pi_of_isRegular (h2 : IsRegular (2 : R)) [∀ c, (P c).IsReduced] :
    (pi P).IsReduced where
  eq_or_eq_neg := by
    rintro ⟨c, i⟩ ⟨d, j⟩ hdep
    by_cases hcd : c = d
    · subst hcd
      have hdep' : ¬ LinearIndependent R ![(P c).root i, (P c).root j] := fun hli ↦ hdep <| by
        convert hli.map' (LinearMap.single R M c) (LinearMap.ker_single R M c) using 1
        ext k
        fin_cases k <;> rfl
      rcases IsReduced.eq_or_eq_neg (P := P c) i j hdep' with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr (by simp [h, Pi.single_neg])
    · exfalso
      refine hdep (LinearIndependent.pair_iff.mpr fun a b hab ↦ ?_)
      have hc : a • (P c).root i = 0 := by
        simpa [Pi.single_eq_of_ne hcd] using congrFun hab c
      have hd : b • (P d).root j = 0 := by
        simpa [Pi.single_eq_of_ne (Ne.symm hcd)] using congrFun hab d
      have ha2 : a * (2 : R) = 0 := by
        have := congrArg ((P c).coroot' i) hc
        simpa [map_smul, smul_eq_mul, root_coroot'_eq_pairing] using this
      have hb2 : b * (2 : R) = 0 := by
        have := congrArg ((P d).coroot' j) hd
        simpa [map_smul, smul_eq_mul, root_coroot'_eq_pairing] using this
      exact ⟨h2.right (by simpa using ha2), h2.right (by simpa using hb2)⟩

/-- A finite direct sum of reduced root pairings over a ring with no zero divisors (and `2 ≠ 0`) is
reduced. -/
instance isReduced_pi [NoZeroDivisors R] [∀ c, (P c).IsReduced] : (pi P).IsReduced :=
  isReduced_pi_of_isRegular P (IsRegular.of_ne_zero' two_ne_zero)

/-! ### Canonical bilinear form and anisotropy -/

section RootForm

variable [∀ c, Fintype (ι c)]

@[simp]
theorem pi_polarization_apply (x : ∀ c, M c) (c : κ) :
    (pi P).Polarization x c = (P c).Polarization (x c) := by
  simp only [Polarization_apply, Fintype.sum_sigma, Finset.sum_apply, Pi.smul_apply, pi_coroot,
    pi_coroot'_apply]
  rw [Finset.sum_eq_single_of_mem c (Finset.mem_univ c)]
  · simp
  · intro d _ hdc
    simp [Pi.single_eq_of_ne (Ne.symm hdc)]

/-- **The canonical bilinear form of a finite direct sum is the orthogonal sum of the summands'
canonical forms.** -/
@[simp]
theorem pi_rootForm_apply_apply (x y : ∀ c, M c) :
    (pi P).RootForm x y = ∑ c, (P c).RootForm (x c) (y c) := by
  simp only [rootForm_apply_apply, Fintype.sum_sigma, pi_coroot'_apply]

@[simp]
theorem pi_corootForm_apply_apply (x y : ∀ c, N c) :
    (pi P).CorootForm x y = ∑ c, (P c).CorootForm (x c) (y c) := by
  simp only [corootForm_apply_apply, Fintype.sum_sigma, pi_root'_apply]

/-- A finite direct sum of anisotropic finite root pairings is anisotropic. -/
instance isAnisotropic_pi [∀ c, (P c).IsAnisotropic] : (pi P).IsAnisotropic where
  rootForm_root_ne_zero := by
    rintro ⟨c, i⟩
    rw [pi_rootForm_apply_apply, Finset.sum_eq_single_of_mem c (Finset.mem_univ c)]
    · simpa using IsAnisotropic.rootForm_root_ne_zero (P := P c) i
    · intro d _ hdc
      simp [Pi.single_eq_of_ne hdc]
  corootForm_coroot_ne_zero := by
    rintro ⟨c, i⟩
    rw [pi_corootForm_apply_apply, Finset.sum_eq_single_of_mem c (Finset.mem_univ c)]
    · simpa using IsAnisotropic.corootForm_coroot_ne_zero (P := P c) i
    · intro d _ hdc
      simp [Pi.single_eq_of_ne hdc]

end RootForm

/-! ### Bases, positive roots, cones, dominance, and chambers -/

/-- **The base of a finite direct sum of root pairings** assembled from bases of its summands.
Its simple-root support is the disjoint union `Finset.univ.sigma fun c ↦ (b c).support`. -/
noncomputable def Base.pi {P : ∀ c, RootPairing (ι c) R (M c) (N c)} (b : ∀ c, (P c).Base) :
    (RootPairing.pi P).Base where
  support := Finset.univ.sigma fun c ↦ (b c).support
  linearIndepOn_root := by
    have hroot : ⇑(RootPairing.pi P).root = fun p : Σ c, ι c ↦ Pi.single p.1 ((P p.1).root p.2) :=
      funext fun ⟨c, i⟩ ↦ pi_root P c i
    rw [hroot, Finset.coe_sigma, Finset.coe_univ]
    exact (Pi.linearIndepOn_single_iff fun c ↦ (P c).root).mpr fun c _ ↦ (b c).linearIndepOn_root
  linearIndepOn_coroot := by
    have hcoroot : ⇑(RootPairing.pi P).coroot =
        fun p : Σ c, ι c ↦ Pi.single p.1 ((P p.1).coroot p.2) :=
      funext fun ⟨c, i⟩ ↦ pi_coroot P c i
    rw [hcoroot, Finset.coe_sigma, Finset.coe_univ]
    exact (Pi.linearIndepOn_single_iff fun c ↦ (P c).coroot).mpr
      fun c _ ↦ (b c).linearIndepOn_coroot
  root_mem_or_neg_mem := by
    rintro ⟨c, i⟩
    have hmono : AddSubmonoid.closure (Pi.single c '' ((P c).root '' (b c).support)) ≤
        AddSubmonoid.closure ((RootPairing.pi P).root ''
          ((Finset.univ.sigma fun d ↦ (b d).support : Finset (Σ d, ι d)) : Set (Σ d, ι d))) :=
      AddSubmonoid.closure_mono <| by
        rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        exact ⟨⟨c, j⟩, by simpa using hj, pi_root P c j⟩
    rw [pi_root]
    rcases (b c).root_mem_or_neg_mem i with h | h
    · exact Or.inl (hmono (AddSubmonoid.single_mem_closure_iff.mpr h))
    · exact Or.inr <| by
        simpa [Pi.single_neg] using hmono (AddSubmonoid.single_mem_closure_iff.mpr h)
  coroot_mem_or_neg_mem := by
    rintro ⟨c, i⟩
    have hmono : AddSubmonoid.closure (Pi.single c '' ((P c).coroot '' (b c).support)) ≤
        AddSubmonoid.closure ((RootPairing.pi P).coroot ''
          ((Finset.univ.sigma fun d ↦ (b d).support : Finset (Σ d, ι d)) : Set (Σ d, ι d))) :=
      AddSubmonoid.closure_mono <| by
        rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        exact ⟨⟨c, j⟩, by simpa using hj, pi_coroot P c j⟩
    rw [pi_coroot]
    rcases (b c).coroot_mem_or_neg_mem i with h | h
    · exact Or.inl (hmono (AddSubmonoid.single_mem_closure_iff.mpr h))
    · exact Or.inr <| by
        simpa [Pi.single_neg] using hmono (AddSubmonoid.single_mem_closure_iff.mpr h)

variable {P}

@[simp]
theorem Base.support_pi (b : ∀ c, (P c).Base) :
    (Base.pi b).support = Finset.univ.sigma fun c ↦ (b c).support :=
  (rfl)

theorem Base.mem_support_pi (b : ∀ c, (P c).Base) (s : Σ c, ι c) :
    s ∈ (Base.pi b).support ↔ s.2 ∈ (b s.1).support := by
  simp

@[simp]
theorem Base.cartanMatrixIn_pi_same (S : Type*) [CommRing S] [Algebra S R] [FaithfulSMul S R]
    [∀ c, (P c).IsValuedIn S] (b : ∀ c, (P c).Base) (c : κ)
    (i j : (b c).support) :
    (Base.pi b).cartanMatrixIn S ⟨⟨c, i.1⟩, by simp [i.2]⟩ ⟨⟨c, j.1⟩, by simp [j.2]⟩ =
      (b c).cartanMatrixIn S i j := by
  simp [Base.cartanMatrixIn_def]

@[simp]
theorem Base.cartanMatrixIn_pi_ne (S : Type*) [CommRing S] [Algebra S R] [FaithfulSMul S R]
    [∀ c, (P c).IsValuedIn S] (b : ∀ c, (P c).Base) {c d : κ} (hcd : c ≠ d)
    (i : (b c).support) (j : (b d).support) :
    (Base.pi b).cartanMatrixIn S ⟨⟨c, i.1⟩, by simp [i.2]⟩ ⟨⟨d, j.1⟩, by simp [j.2]⟩ = 0 := by
  simp [Base.cartanMatrixIn_def, pi_pairingIn_ne P S hcd]

/-- The height of a root in a finite direct sum is its height in its own summand. -/
@[simp]
theorem Base.height_pi [CharZero R] (b : ∀ c, (P c).Base) (c : κ) (i : ι c) :
    (Base.pi b).height ⟨c, i⟩ = (b c).height i := by
  obtain ⟨f, -, -, hf⟩ := (b c).exists_root_eq_sum_int i
  let g : (Σ d, ι d) → ℤ := fun p ↦ if h : p.1 = c then f (h ▸ p.2) else 0
  have hg : (RootPairing.pi P).root ⟨c, i⟩ =
      ∑ p ∈ (Base.pi b).support, g p • (RootPairing.pi P).root p := by
    rw [Base.support_pi, Finset.sum_sigma, Finset.sum_eq_single_of_mem c (Finset.mem_univ c)]
    · simp only [g, ↓reduceDIte, pi_root, hf]
      rw [← LinearMap.single_apply (R := R) (φ := M), map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp [map_zsmul]
    · intro d _ hdc
      simp [g, hdc]
  rw [(Base.pi b).height_eq_sum hg, (b c).height_eq_sum hf, Base.support_pi, Finset.sum_sigma,
    Finset.sum_eq_single_of_mem c (Finset.mem_univ c)]
  · simp [g]
  · intro d _ hdc
    simp [g, hdc]

/-- A root of a finite direct sum is positive for `Base.pi b` iff it is positive in its summand. -/
@[simp]
theorem Base.isPos_pi_iff [CharZero R] (b : ∀ c, (P c).Base) (c : κ) (i : ι c) :
    (Base.pi b).IsPos ⟨c, i⟩ ↔ (b c).IsPos i := by
  simp [Base.isPos_iff]

/-- Membership in `posRoots` of a finite direct sum is membership in the summand's `posRoots`. -/
theorem mem_posRoots_pi_iff [CharZero R] (b : ∀ c, (P c).Base) (c : κ) (i : ι c) :
    ⟨c, i⟩ ∈ TauCeti.posRoots (pi P) (Base.pi b) ↔ i ∈ TauCeti.posRoots (P c) (b c) := by
  simp only [TauCeti.mem_posRoots, Base.isPos_pi_iff]

/-- **The positive root cone of a finite direct sum decomposes coordinatewise.** -/
theorem mem_posRootCone_pi_iff (b : ∀ c, (P c).Base) (x : ∀ c, M c) :
    x ∈ TauCeti.posRootCone (pi P) (Base.pi b) ↔
      ∀ c, x c ∈ TauCeti.posRootCone (P c) (b c) := by
  simp only [TauCeti.mem_posRootCone]
  constructor
  · rintro ⟨n, hx⟩ c
    refine ⟨fun i ↦ n ⟨c, i⟩, ?_⟩
    have hxc := congrFun hx c
    rw [Base.support_pi, Finset.sum_sigma, Finset.sum_apply] at hxc
    rw [hxc, Finset.sum_eq_single_of_mem c (Finset.mem_univ c)]
    · simp
    · intro d _ hdc
      simp [Pi.single_eq_of_ne (Ne.symm hdc)]
  · intro h
    choose n hn using h
    refine ⟨fun p ↦ n p.1 p.2, ?_⟩
    ext c
    rw [Base.support_pi, Finset.sum_sigma, Finset.sum_apply,
      Finset.sum_eq_single_of_mem c (Finset.mem_univ c)]
    · simp [hn c]
    · intro d _ hdc
      simp [Pi.single_eq_of_ne (Ne.symm hdc)]

/-- **Integral root dominance on a finite direct sum is coordinatewise integral root dominance.** -/
theorem rootLE_pi_iff (b : ∀ c, (P c).Base) (x y : ∀ c, M c) :
    (pi P).rootLE (Base.pi b) x y ↔ ∀ c, (P c).rootLE (b c) (x c) (y c) := by
  simpa [rootLE_iff_sub_mem_posRootCone] using mem_posRootCone_pi_iff b (y - x)

/-- A weight of a finite direct sum is regular iff every coordinate is regular. -/
theorem isRegularWeight_pi_iff (x : ∀ c, M c) :
    (pi P).IsRegularWeight x ↔ ∀ c, (P c).IsRegularWeight (x c) := by
  simp [isRegularWeight_iff, Sigma.forall]

/-- **The closed dominant chamber of a finite direct sum decomposes coordinatewise.** -/
theorem mem_dominantChamber_pi_iff [Preorder R] (b : ∀ c, (P c).Base) (x : ∀ c, M c) :
    x ∈ (pi P).dominantChamber (Base.pi b) ↔ ∀ c, x c ∈ (P c).dominantChamber (b c) := by
  simp [mem_dominantChamber, Sigma.forall]

/-- **The open dominant chamber of a finite direct sum decomposes coordinatewise.** -/
theorem mem_openDominantChamber_pi_iff [Preorder R] (b : ∀ c, (P c).Base) (x : ∀ c, M c) :
    x ∈ (pi P).openDominantChamber (Base.pi b) ↔ ∀ c, x c ∈ (P c).openDominantChamber (b c) := by
  simp [mem_openDominantChamber, Sigma.forall]

end Basic

/-! ### Functoriality and the Weyl group -/

section Functoriality

variable {κ κ' R : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
  [CommRing R] [NeZero (2 : R)]
  {ι M N : κ → Type*}
  [∀ c, AddCommGroup (M c)] [∀ c, Module R (M c)]
  [∀ c, AddCommGroup (N c)] [∀ c, Module R (N c)]
  {ι' M' N' : κ' → Type*}
  [∀ c, AddCommGroup (M' c)] [∀ c, Module R (M' c)]
  [∀ c, AddCommGroup (N' c)] [∀ c, Module R (N' c)]
  {P : ∀ c, RootPairing (ι c) R (M c) (N c)}
  {Q : ∀ c, RootPairing (ι' c) R (M' c) (N' c)}

/-- **Functoriality of finite direct sums of root pairings**: a bijection `eκ : κ ≃ κ'` of summand
indices together with equivalences `e c : (P c).Equiv (Q (eκ c))` induces an equivalence between
`RootPairing.pi P` and `RootPairing.pi Q`. -/
noncomputable def Equiv.piCongr (eκ : κ ≃ κ') (e : ∀ c, (P c).Equiv (Q (eκ c))) :
    (pi P).Equiv (pi Q) where
  weightMap := (LinearEquiv.piCongrRight fun c ↦ (e c).weightEquiv).trans
    (LinearEquiv.piCongrLeft R M' eκ)
  coweightMap := ((LinearEquiv.piCongrLeft R N' eκ).symm.trans
    (LinearEquiv.piCongrRight fun c ↦ (e c).coweightEquiv)).toLinearMap
  indexEquiv := _root_.Equiv.sigmaCongr eκ fun c ↦ (e c).indexEquiv
  weight_coweight_transpose := by
    refine LinearMap.ext fun y ↦ LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.dualMap_apply, LinearEquiv.coe_coe,
      LinearEquiv.trans_apply, LinearMap.toPerfPair_apply, flip_toLinearMap, LinearMap.flip_apply,
      pi_toLinearMap_apply]
    rw [← eκ.sum_comp]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    have h1 : (LinearEquiv.piCongrLeft R M' eκ
        (LinearEquiv.piCongrRight (fun c ↦ (e c).weightEquiv) x)) (eκ c) =
        (e c).weightEquiv (x c) := by
      simp [LinearEquiv.piCongrLeft_apply_apply]
    have h2 : (LinearEquiv.piCongrRight (fun c ↦ (e c).coweightEquiv)
        ((LinearEquiv.piCongrLeft R N' eκ).symm y)) c = (e c).coweightEquiv (y (eκ c)) := rfl
    rw [h1, h2]
    exact (e c).toLinearMap_weightEquiv (x c) (y (eκ c))
  root_weightMap := by
    ext ⟨c, i⟩ d
    simp [Hom.root_weightMap_apply, _root_.Equiv.sigmaCongr]
  coroot_coweightMap := by
    ext ⟨d, j⟩ c
    obtain ⟨c', rfl⟩ := eκ.surjective d
    have hidx : (_root_.Equiv.sigmaCongr eκ fun c ↦ (e c).indexEquiv).symm ⟨eκ c', j⟩ =
        ⟨c', (e c').indexEquiv.symm j⟩ := by
      rw [_root_.Equiv.symm_apply_eq]
      simp [_root_.Equiv.sigmaCongr]
    simp only [comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      LinearEquiv.piCongrRight_apply, hidx, pi_coroot]
    have hsymm : (LinearEquiv.piCongrLeft R N' eκ).symm
        (Pi.single (eκ c') ((Q (eκ c')).coroot j)) c =
        Pi.single (eκ c') ((Q (eκ c')).coroot j) (eκ c) := rfl
    rw [hsymm]
    by_cases h : c = c'
    · subst h
      simp [Hom.coroot_coweightMap_apply]
    · simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (eκ.injective.ne h)]
  bijective_weightMap := LinearEquiv.bijective _
  bijective_coweightMap := LinearEquiv.bijective _

@[simp]
theorem Equiv.piCongr_indexEquiv (eκ : κ ≃ κ') (e : ∀ c, (P c).Equiv (Q (eκ c)))
    (c : κ) (i : ι c) :
    (Equiv.piCongr eκ e).indexEquiv ⟨c, i⟩ = ⟨eκ c, (e c).indexEquiv i⟩ :=
  (rfl)

@[simp]
theorem Equiv.piCongr_weightMap_apply (eκ : κ ≃ κ') (e : ∀ c, (P c).Equiv (Q (eκ c)))
    (x : ∀ c, M c) (c : κ) :
    (Equiv.piCongr eκ e).weightMap x (eκ c) = (e c).weightMap (x c) := by
  simp [Equiv.piCongr, LinearEquiv.piCongrLeft_apply_apply]

@[simp]
theorem Equiv.piCongr_coweightMap_apply (eκ : κ ≃ κ') (e : ∀ c, (P c).Equiv (Q (eκ c)))
    (y : ∀ c, N' c) (c : κ) :
    (Equiv.piCongr eκ e).coweightMap y c = (e c).coweightMap (y (eκ c)) :=
  (rfl)

end Functoriality

section WeylGroup

variable {κ R : Type*} [Fintype κ] [DecidableEq κ] [CommRing R] [NeZero (2 : R)]
  {ι M N : κ → Type*}
  [∀ c, AddCommGroup (M c)] [∀ c, Module R (M c)]
  [∀ c, AddCommGroup (N c)] [∀ c, Module R (N c)]
  (P : ∀ c, RootPairing (ι c) R (M c) (N c))

/-- The canonical embedding of the product of summand automorphism groups into the automorphism
group of `RootPairing.pi P`. -/
noncomputable def piAut : (∀ c, (P c).Aut) →* (pi P).Aut where
  toFun g := Equiv.piCongr (_root_.Equiv.refl κ) g
  map_one' := by
    refine Equiv.weightHom_injective (pi P) (LinearEquiv.ext fun x ↦ funext fun c ↦ ?_)
    have h := Equiv.piCongr_weightMap_apply (_root_.Equiv.refl κ) (1 : ∀ c, (P c).Aut) x c
    simp only [Equiv.weightHom_apply, Equiv.weightEquiv_apply, _root_.Equiv.refl_apply,
      Pi.one_apply] at h ⊢
    rw [h]
    rfl
  map_mul' g h := by
    refine Equiv.weightHom_injective (pi P) (LinearEquiv.ext fun x ↦ funext fun c ↦ ?_)
    have h1 := Equiv.piCongr_weightMap_apply (_root_.Equiv.refl κ) (g * h) x c
    have h2 := Equiv.piCongr_weightMap_apply (_root_.Equiv.refl κ) g
      ((Equiv.piCongr (_root_.Equiv.refl κ) h).weightMap x) c
    have h3 := Equiv.piCongr_weightMap_apply (_root_.Equiv.refl κ) h x c
    simpa [Equiv.weightHom_apply, Equiv.weightEquiv_apply, h3] using h1.trans h2.symm

@[simp]
theorem piAut_weightMap_apply (g : ∀ c, (P c).Aut) (x : ∀ c, M c) (c : κ) :
    (piAut P g).weightMap x c = (g c).weightMap (x c) :=
  Equiv.piCongr_weightMap_apply (_root_.Equiv.refl κ) g x c

@[simp]
theorem piAut_coweightMap_apply (g : ∀ c, (P c).Aut) (y : ∀ c, N c) (c : κ) :
    (piAut P g).coweightMap y c = (g c).coweightMap (y c) :=
  Equiv.piCongr_coweightMap_apply (_root_.Equiv.refl κ) g y c

@[simp]
theorem piAut_indexEquiv (g : ∀ c, (P c).Aut) (c : κ) (i : ι c) :
    (piAut P g).indexEquiv ⟨c, i⟩ = ⟨c, (g c).indexEquiv i⟩ :=
  Equiv.piCongr_indexEquiv (_root_.Equiv.refl κ) g c i

/-- `RootPairing.piAut` is injective: an automorphism of `RootPairing.pi P` in its image
determines every coordinate automorphism. -/
theorem piAut_injective : Function.Injective (piAut P) := by
  intro g h hgh
  funext c
  refine Equiv.weightHom_injective (P c) (LinearEquiv.ext fun x ↦ ?_)
  have h1 := congrFun (congrArg (fun a : (pi P).Aut ↦ a.weightMap (Pi.single c x)) hgh) c
  simpa using h1

/-- Inserting a single reflection at coordinate `c` maps under `piAut` to the reflection of the
direct sum at `⟨c, i⟩`. -/
@[simp]
theorem piAut_mulSingle_reflection (c : κ) (i : ι c) :
    piAut P (Pi.mulSingle c (Equiv.reflection (P c) i)) = Equiv.reflection (pi P) ⟨c, i⟩ := by
  refine Equiv.weightHom_injective (pi P) (LinearEquiv.ext fun x ↦ funext fun d ↦ ?_)
  by_cases h : d = c
  · subst h
    simp only [Equiv.weightHom_apply, Equiv.weightEquiv_apply, piAut_weightMap_apply,
      Pi.mulSingle_eq_same, Equiv.reflection_weightEquiv, pi_reflection_apply_same]
    exact LinearEquiv.congr_fun (Equiv.reflection_weightEquiv (P d) i) (x d)
  · simp [Equiv.weightHom_apply, Equiv.reflection_weightEquiv, h]

/-- Each single-coordinate Weyl-group element lands in `(pi P).weylGroup` under `piAut`. -/
private theorem piAut_mulSingle_mem_weylGroup (c : κ) {a : (P c).Aut} (ha : a ∈ (P c).weylGroup) :
    piAut P (Pi.mulSingle c a) ∈ (pi P).weylGroup := by
  induction ha using weylGroup.induction with
  | mem i =>
    rw [piAut_mulSingle_reflection]
    exact Subgroup.subset_closure ⟨⟨c, i⟩, rfl⟩
  | one =>
    rw [Pi.mulSingle_one, map_one]
    exact (pi P).weylGroup.one_mem
  | mul a b _ _ ha hb =>
    rw [Pi.mulSingle_mul, map_mul]
    exact (pi P).weylGroup.mul_mem ha hb

/-- Every product of summand Weyl-group elements lands in `(pi P).weylGroup` under `piAut`. -/
private theorem piAut_mem_weylGroup (w : ∀ c, (P c).weylGroup) :
    piAut P (fun c ↦ (w c : (P c).Aut)) ∈ (pi P).weylGroup := by
  suffices ∀ s : Finset κ,
      piAut P (fun c ↦ if c ∈ s then (w c : (P c).Aut) else 1) ∈ (pi P).weylGroup by
    simpa using this Finset.univ
  intro s
  induction s using Finset.cons_induction with
  | empty =>
    have h1 : (fun c : κ ↦ (1 : (P c).Aut)) = 1 := rfl
    simp only [Finset.notMem_empty, ↓reduceIte, h1, map_one]
    exact (pi P).weylGroup.one_mem
  | cons a s ha ih =>
    have hsplit : (fun c ↦ if c ∈ Finset.cons a s ha then (w c : (P c).Aut) else 1) =
        Pi.mulSingle a (w a : (P a).Aut) * (fun c ↦ if c ∈ s then (w c : (P c).Aut) else 1) := by
      funext c
      by_cases hc : c = a
      · subst hc
        simp [ha]
      · simp [hc]
    rw [hsplit, map_mul]
    exact (pi P).weylGroup.mul_mem (piAut_mulSingle_mem_weylGroup P a (w a).2) ih

/-- The homomorphism `(∀ c, (P c).weylGroup) →* (pi P).weylGroup` induced by `piAut`. -/
private noncomputable def piWeylGroupHom : (∀ c, (P c).weylGroup) →* (pi P).weylGroup where
  toFun w := ⟨piAut P fun c ↦ (w c : (P c).Aut), piAut_mem_weylGroup P w⟩
  map_one' := Subtype.ext (map_one (piAut P))
  map_mul' _ _ := Subtype.ext (map_mul (piAut P) _ _)

/-- **The Weyl group of a finite direct sum is canonically isomorphic to the product of the
Weyl groups of its summands.** -/
noncomputable def piWeylGroupEquiv : (pi P).weylGroup ≃* ∀ c, (P c).weylGroup :=
  (MulEquiv.ofBijective (piWeylGroupHom P)
    ⟨fun _ _ h ↦ funext fun c ↦ Subtype.ext
        (congrFun (piAut_injective P (congrArg Subtype.val h)) c),
     by
      rintro ⟨g, hg⟩
      induction hg using weylGroup.induction with
      | mem s =>
        rcases s with ⟨c, i⟩
        let w : ∀ d, (P d).weylGroup := Pi.mulSingle c (weylGroup.ofIdx (P c) i)
        refine ⟨w, Subtype.ext ?_⟩
        have hval : (fun d ↦ (w d : (P d).Aut)) = Pi.mulSingle c (Equiv.reflection (P c) i) := by
          funext d
          by_cases h : d = c
          · subst h; simp [w]
          · simp [w, Pi.mulSingle_eq_of_ne h]
        simp [piWeylGroupHom, hval]
      | one => exact ⟨1, map_one _⟩
      | mul a b _ _ iha ihb =>
        rcases iha with ⟨wa, hwa⟩
        rcases ihb with ⟨wb, hwb⟩
        exact ⟨wa * wb, by rw [map_mul, hwa, hwb]; rfl⟩⟩).symm

@[simp]
theorem coe_piWeylGroupEquiv_symm (w : ∀ c, (P c).weylGroup) :
    ((piWeylGroupEquiv P).symm w : (pi P).Aut) = piAut P fun c ↦ (w c : (P c).Aut) :=
  (rfl)

theorem piWeylGroupEquiv_symm_smul (w : ∀ c, (P c).weylGroup) (x : ∀ c, M c) (c : κ) :
    ((piWeylGroupEquiv P).symm w • x) c = w c • x c :=
  piAut_weightMap_apply P (fun d ↦ (w d : (P d).Aut)) x c

@[simp]
theorem piWeylGroupEquiv_smul (w : (pi P).weylGroup) (x : ∀ c, M c) (c : κ) :
    (w • x) c = piWeylGroupEquiv P w c • x c := by
  simpa using piWeylGroupEquiv_symm_smul P (piWeylGroupEquiv P w) x c

/-- The Weyl-group isomorphism matches each reflection of the direct sum with the single-coordinate
reflection in the product of Weyl groups. -/
@[simp]
theorem piWeylGroupEquiv_ofIdx (c : κ) (i : ι c) :
    piWeylGroupEquiv P (weylGroup.ofIdx (pi P) ⟨c, i⟩) =
      Pi.mulSingle c (weylGroup.ofIdx (P c) i) := by
  refine (piWeylGroupEquiv P).symm.injective ?_
  rw [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  rw [coe_piWeylGroupEquiv_symm, weylGroup.coe_ofIdx]
  refine (piAut_mulSingle_reflection P c i).symm.trans ?_
  congr 1
  funext d
  by_cases h : d = c
  · subst h; simp
  · simp [Pi.mulSingle_eq_of_ne h]

end WeylGroup

end RootPairing
