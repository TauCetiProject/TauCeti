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
public import TauCeti.LinearAlgebra.RootSystem.Basic
public import TauCeti.LinearAlgebra.RootSystem.Height
import Mathlib.Algebra.Ring.Regular
import TauCeti.LinearAlgebra.LinearIndependent.Pi

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
`RootPairing.Base.pi` and split back into `RootPairing.Base.restrictPi`; the Cartan matrix of
`Base.pi` is block diagonal, heights and positivity decompose coordinatewise, and
`RootPairing.Equiv.piCongr` transports assembled bases to assembled bases. The canonical bilinear
forms `RootForm` and `CorootForm` are the orthogonal sums of the summands' forms.

## Main definitions

* `RootPairing.pi`: the finite external direct sum of a family of root pairings.
* `RootPairing.Base.pi`: the base of `RootPairing.pi P` assembled from a base of each summand.
* `RootPairing.Base.restrictPi`: the restriction of a base of `RootPairing.pi P` to a summand.
* `RootPairing.Equiv.piCongr`: functoriality of `RootPairing.pi` under reindexing and summand
  equivalences.

## Main results

* `RootPairing.range_pi_root`: the roots of `RootPairing.pi P` are the union of the coordinate
  images of the summands' roots.
* `RootPairing.pi_flip`: flipping a finite direct sum gives the direct sum of the flipped pairings.
* `RootPairing.isRootSystem_pi`, `RootPairing.isValuedIn_pi`, `RootPairing.isReduced_pi`,
  `RootPairing.isAnisotropic_pi`: structural instances preserved by finite direct sums.
* `RootPairing.pi_rootForm_apply_apply`, `RootPairing.pi_corootForm_apply_apply`: the canonical
  bilinear forms split as the orthogonal sums of the summands' forms.
* `RootPairing.Base.height_pi`, `RootPairing.Base.isPos_pi_iff`,
  `RootPairing.Base.pi_restrictPi`, `RootPairing.Base.restrictPi_pi`,
  `RootPairing.Base.map_piCongr_pi`: coordinatewise decomposition and transport of bases, heights,
  and positivity.

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
  have h : ⇑(pi P).root = fun s : Σ c, ι c ↦ Pi.single s.1 ((P s.1).root s.2) := rfl
  rw [h, Set.range_sigma_eq_iUnion_range]
  exact iUnion_congr fun c ↦ Set.range_comp' (Pi.single c) (P c).root

/-- The coroots of a finite direct sum are the union of the coordinate images of the summands'
coroots. -/
theorem range_pi_coroot :
    range (pi P).coroot = ⋃ c, Pi.single c '' range (P c).coroot :=
  range_pi_root fun c ↦ (P c).flip

/-- Flipping a finite direct sum of root pairings gives the finite direct sum of the flipped
pairings. -/
@[simp]
theorem pi_flip : (pi P).flip = pi fun c ↦ (P c).flip :=
  ext_of_coroot (LinearMap.flip_piPairing _) rfl rfl

/-! ### Structural properties -/

/-- An element of `∀ c, M c` lies in the `S`-span of the coordinate images of `(P c).root '' s c`
if and only if each coordinate lies in the `S`-span of `(P c).root '' s c`. -/
theorem mem_span_pi_root_image_iff (S : Type*) [Semiring S] [∀ c, Module S (M c)]
    (s : ∀ c, Set (ι c)) (x : ∀ c, M c) :
    x ∈ span S ((pi P).root '' (Set.univ.sigma s)) ↔ ∀ c, x c ∈ span S ((P c).root '' s c) := by
  have himage : (pi P).root '' (Set.univ.sigma s) = ⋃ c, Pi.single c '' ((P c).root '' s c) := by
    ext v
    simp [Set.mem_sigma_iff]
  rw [himage, Submodule.span_iUnion]
  have hsingle (c : κ) : span S (Pi.single c '' ((P c).root '' s c)) =
      (span S ((P c).root '' s c)).map (LinearMap.single S M c) := by
    rw [show Pi.single c '' ((P c).root '' s c) =
      (LinearMap.single S M c) '' ((P c).root '' s c) from rfl, ← Submodule.map_span]
  simp_rw [hsingle, Submodule.iSup_map_single, Submodule.mem_pi, Set.mem_univ, forall_true_left]

/-- The `S`-span of the roots of a finite direct sum is the coordinatewise product of the
summands' root spans. -/
theorem mem_rootSpan_pi_iff (S : Type*) [Semiring S] [∀ c, Module S (M c)] (x : ∀ c, M c) :
    x ∈ span S (range (pi P).root) ↔ ∀ c, x c ∈ span S (range (P c).root) := by
  simpa using mem_span_pi_root_image_iff P S (fun _ ↦ Set.univ) x

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
    have hmono : (AddSubmonoid.closure ((P c).root '' (b c).support)).map
          (AddMonoidHom.single M c) ≤
        AddSubmonoid.closure ((RootPairing.pi P).root ''
          ((Finset.univ.sigma fun d ↦ (b d).support : Finset (Σ d, ι d)) : Set (Σ d, ι d))) := by
      rw [AddMonoidHom.map_mclosure]
      refine AddSubmonoid.closure_mono ?_
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      exact ⟨⟨c, j⟩, by simpa using hj, pi_root P c j⟩
    rw [pi_root]
    rcases (b c).root_mem_or_neg_mem i with h | h
    · exact Or.inl (hmono (AddSubmonoid.mem_map_of_mem (AddMonoidHom.single M c) h))
    · exact Or.inr <| by
        simpa [Pi.single_neg] using hmono (AddSubmonoid.mem_map_of_mem (AddMonoidHom.single M c) h)
  coroot_mem_or_neg_mem := by
    rintro ⟨c, i⟩
    have hmono : (AddSubmonoid.closure ((P c).coroot '' (b c).support)).map
          (AddMonoidHom.single N c) ≤
        AddSubmonoid.closure ((RootPairing.pi P).coroot ''
          ((Finset.univ.sigma fun d ↦ (b d).support : Finset (Σ d, ι d)) : Set (Σ d, ι d))) := by
      rw [AddMonoidHom.map_mclosure]
      refine AddSubmonoid.closure_mono ?_
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      exact ⟨⟨c, j⟩, by simpa using hj, pi_coroot P c j⟩
    rw [pi_coroot]
    rcases (b c).coroot_mem_or_neg_mem i with h | h
    · exact Or.inl (hmono (AddSubmonoid.mem_map_of_mem (AddMonoidHom.single N c) h))
    · exact Or.inr <| by
        simpa [Pi.single_neg] using hmono (AddSubmonoid.mem_map_of_mem (AddMonoidHom.single N c) h)

variable {P}

@[simp]
theorem Base.support_pi (b : ∀ c, (P c).Base) :
    (Base.pi b).support = Finset.univ.sigma fun c ↦ (b c).support :=
  (rfl)

/-- **Restricting a base of `RootPairing.pi P` to a summand** by taking the simple roots lying in
that summand. -/
noncomputable def Base.restrictPi (b : (RootPairing.pi P).Base) (c : κ) : (P c).Base where
  support := b.support.preimage (Sigma.mk c) sigma_mk_injective.injOn
  linearIndepOn_root := by
    refine LinearIndependent.of_comp (LinearMap.single R M c) ?_
    refine b.linearIndepOn_root.comp (fun i : {i // i ∈ b.support.preimage (Sigma.mk c)
        sigma_mk_injective.injOn} ↦ ⟨⟨c, i.val⟩, Finset.mem_preimage.mp i.property⟩) ?_
    intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    simpa using hij
  linearIndepOn_coroot := by
    refine LinearIndependent.of_comp (LinearMap.single R N c) ?_
    refine b.linearIndepOn_coroot.comp (fun i : {i // i ∈ b.support.preimage (Sigma.mk c)
        sigma_mk_injective.injOn} ↦ ⟨⟨c, i.val⟩, Finset.mem_preimage.mp i.property⟩) ?_
    intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    simpa using hij
  root_mem_or_neg_mem i := by
    have hle : (AddSubmonoid.closure
          ((RootPairing.pi P).root '' (b.support : Set (Σ d, ι d)))).map
          (Pi.evalAddMonoidHom M c) ≤
        AddSubmonoid.closure ((P c).root '' ((b.support.preimage (Sigma.mk c)
          sigma_mk_injective.injOn : Finset (ι c)) : Set (ι c))) := by
      rw [AddMonoidHom.map_mclosure, AddSubmonoid.closure_le]
      rintro _ ⟨_, ⟨⟨d, j⟩, hj, rfl⟩, rfl⟩
      by_cases hdc : d = c
      · subst hdc
        exact AddSubmonoid.subset_closure ⟨j, by simpa using hj, by simp⟩
      · simp [Pi.single_eq_of_ne (Ne.symm hdc), zero_mem]
    rcases b.root_mem_or_neg_mem ⟨c, i⟩ with h | h
    · exact Or.inl <| by
        simpa using hle (AddSubmonoid.mem_map_of_mem (Pi.evalAddMonoidHom M c) h)
    · exact Or.inr <| by
        simpa using hle (AddSubmonoid.mem_map_of_mem (Pi.evalAddMonoidHom M c) h)
  coroot_mem_or_neg_mem i := by
    have hle : (AddSubmonoid.closure
          ((RootPairing.pi P).coroot '' (b.support : Set (Σ d, ι d)))).map
          (Pi.evalAddMonoidHom N c) ≤
        AddSubmonoid.closure ((P c).coroot '' ((b.support.preimage (Sigma.mk c)
          sigma_mk_injective.injOn : Finset (ι c)) : Set (ι c))) := by
      rw [AddMonoidHom.map_mclosure, AddSubmonoid.closure_le]
      rintro _ ⟨_, ⟨⟨d, j⟩, hj, rfl⟩, rfl⟩
      by_cases hdc : d = c
      · subst hdc
        exact AddSubmonoid.subset_closure ⟨j, by simpa using hj, by simp⟩
      · simp [Pi.single_eq_of_ne (Ne.symm hdc), zero_mem]
    rcases b.coroot_mem_or_neg_mem ⟨c, i⟩ with h | h
    · exact Or.inl <| by
        simpa using hle (AddSubmonoid.mem_map_of_mem (Pi.evalAddMonoidHom N c) h)
    · exact Or.inr <| by
        simpa using hle (AddSubmonoid.mem_map_of_mem (Pi.evalAddMonoidHom N c) h)

@[simp]
theorem Base.mem_support_restrictPi (b : (RootPairing.pi P).Base) (c : κ) (i : ι c) :
    i ∈ (b.restrictPi c).support ↔ ⟨c, i⟩ ∈ b.support := by
  simp [Base.restrictPi]

/-- Assembling the restrictions of a base of `RootPairing.pi P` recovers the original base. -/
@[simp]
theorem Base.pi_restrictPi (b : (RootPairing.pi P).Base) :
    Base.pi (fun c ↦ b.restrictPi c) = b := by
  ext ⟨c, i⟩
  simp

/-- Restricting an assembled base `Base.pi b` to coordinate `c` recovers `b c`. -/
@[simp]
theorem Base.restrictPi_pi (b : ∀ c, (P c).Base) (c : κ) : (Base.pi b).restrictPi c = b c := by
  ext i
  simp

@[simp]
theorem Base.cartanMatrixIn_pi_same (S : Type*) [CommRing S] [Algebra S R] [FaithfulSMul S R]
    [∀ c, (P c).IsValuedIn S] (b : ∀ c, (P c).Base) (c : κ)
    (i j : (b c).support) :
    (Base.pi b).cartanMatrixIn S ⟨⟨c, i.val⟩, by simp [i.property]⟩
        ⟨⟨c, j.val⟩, by simp [j.property]⟩ =
      (b c).cartanMatrixIn S i j := by
  simp [Base.cartanMatrixIn_def]

@[simp]
theorem Base.cartanMatrixIn_pi_ne (S : Type*) [CommRing S] [Algebra S R] [FaithfulSMul S R]
    [∀ c, (P c).IsValuedIn S] (b : ∀ c, (P c).Base) {c d : κ} (hcd : c ≠ d)
    (i : (b c).support) (j : (b d).support) :
    (Base.pi b).cartanMatrixIn S ⟨⟨c, i.val⟩, by simp [i.property]⟩
        ⟨⟨d, j.val⟩, by simp [j.property]⟩ = 0 := by
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

end Basic

/-! ### Functoriality -/

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
        (e c).weightEquiv (x c) :=
      _root_.Equiv.piCongrLeft_apply_apply M' eκ _ c
    have h2 : (LinearEquiv.piCongrRight (fun c ↦ (e c).coweightEquiv)
        ((LinearEquiv.piCongrLeft R N' eκ).symm y)) c = (e c).coweightEquiv (y (eκ c)) := rfl
    rw [h1, h2]
    exact (e c).toLinearMap_weightEquiv (x c) (y (eκ c))
  root_weightMap := by
    ext ⟨c, i⟩ d
    obtain ⟨c', rfl⟩ := eκ.surjective d
    have hidx : (Equiv.sigmaCongr eκ fun c ↦ (e c).indexEquiv) ⟨c, i⟩ =
        ⟨eκ c, (e c).indexEquiv i⟩ := rfl
    simp only [comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply, pi_root]
    rw [hidx, pi_root]
    have h1 : (LinearEquiv.piCongrLeft R M' eκ
        (LinearEquiv.piCongrRight (fun c ↦ (e c).weightEquiv) (Pi.single c ((P c).root i))))
        (eκ c') =
        (LinearEquiv.piCongrRight (fun c ↦ (e c).weightEquiv) (Pi.single c ((P c).root i))) c' :=
      _root_.Equiv.piCongrLeft_apply_apply M' eκ _ c'
    rw [h1, LinearEquiv.piCongrRight_apply]
    by_cases h : c' = c
    · subst h
      simp [Hom.root_weightMap_apply]
    · simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (eκ.injective.ne h)]
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
    (Equiv.piCongr eκ e).weightMap x (eκ c) = (e c).weightMap (x c) :=
  _root_.Equiv.piCongrLeft_apply_apply M' eκ _ c

@[simp]
theorem Equiv.piCongr_coweightMap_apply (eκ : κ ≃ κ') (e : ∀ c, (P c).Equiv (Q (eκ c)))
    (y : ∀ c, N' c) (c : κ) :
    (Equiv.piCongr eκ e).coweightMap y c = (e c).coweightMap (y (eκ c)) :=
  (rfl)

/-- Mapping an assembled base `Base.pi b` along `Equiv.piCongr` produces the assembled base
`Base.pi b'` whenever `e c` carries `b c` to `b' (eκ c)`. -/
theorem Base.map_piCongr_pi (eκ : κ ≃ κ') (e : ∀ c, (P c).Equiv (Q (eκ c)))
    {b : ∀ c, (P c).Base} {b' : ∀ c', (Q c').Base}
    (hb : ∀ c, (b c).map (e c) = b' (eκ c)) :
    (Base.pi b).map (Equiv.piCongr eκ e) = Base.pi b' := by
  classical
  ext ⟨c', j⟩
  obtain ⟨c, rfl⟩ := eκ.surjective c'
  simp only [Base.support_map_eq, Base.support_pi, Finset.mem_image, Finset.mem_sigma,
    Finset.mem_univ, true_and, Sigma.exists]
  constructor
  · rintro ⟨d, i, hi, heq⟩
    rw [Equiv.piCongr_indexEquiv] at heq
    rcases Sigma.ext_iff.mp heq with ⟨hdc, hij⟩
    obtain rfl := eκ.injective hdc
    rw [heq_eq_eq] at hij
    rw [← hb d]
    simp only [Base.support_map_eq, Finset.mem_image]
    exact ⟨i, hi, hij⟩
  · intro hj
    rw [← hb c] at hj
    simp only [Base.support_map_eq, Finset.mem_image] at hj
    obtain ⟨i, hi, hij⟩ := hj
    exact ⟨c, i, hi, by rw [Equiv.piCongr_indexEquiv, hij]⟩

/-- Mapping an assembled base `Base.pi b` along `Equiv.piCongr (.refl κ) e` assembles the
transported summand bases. -/
@[simp]
theorem Base.map_piCongr_refl_pi
    {ι'' M'' N'' : κ → Type*}
    [∀ c, AddCommGroup (M'' c)] [∀ c, Module R (M'' c)]
    [∀ c, AddCommGroup (N'' c)] [∀ c, Module R (N'' c)]
    {Q : ∀ c, RootPairing (ι'' c) R (M'' c) (N'' c)}
    (e : ∀ c, (P c).Equiv (Q c)) (b : ∀ c, (P c).Base) :
    (Base.pi b).map (Equiv.piCongr (_root_.Equiv.refl κ) e) =
      Base.pi fun c ↦ (b c).map (e c) :=
  Base.map_piCongr_pi (_root_.Equiv.refl κ) e fun _ ↦ rfl

end Functoriality

end RootPairing
