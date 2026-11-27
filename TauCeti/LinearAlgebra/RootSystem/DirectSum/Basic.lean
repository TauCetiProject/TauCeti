/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Hom
public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import TauCeti.LinearAlgebra.PerfectPairing.Pi
public import TauCeti.LinearAlgebra.RootSystem.Basic
import Mathlib.Algebra.Ring.Regular
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
`IsCrystallographic`), and reducedness (when `2` is regular, in particular when `R` has no zero
divisors). Functoriality `RootPairing.Equiv.piCongr` preserves identity and composition.

## Main definitions

* `RootPairing.pi`: the finite external direct sum of a family of root pairings.
* `RootPairing.Equiv.piCongr`: functoriality of `RootPairing.pi` under reindexing and summand
  equivalences.

## Main results

* `RootPairing.range_pi_root`: the roots of `RootPairing.pi P` are the union of the coordinate
  images of the summands' roots.
* `RootPairing.pi_flip`: flipping a finite direct sum gives the direct sum of the flipped pairings.
* `RootPairing.isRootSystem_pi_iff`, `RootPairing.isValuedIn_pi_iff`,
  `RootPairing.isReduced_of_pi`, `RootPairing.isReduced_pi_iff_of_isRegular`,
  `RootPairing.isReduced_pi_iff`: structural characterizations for finite direct sums.
* `RootPairing.Equiv.piCongr_id`, `RootPairing.Equiv.piCongr_comp`: identity and composition laws
  for `RootPairing.Equiv.piCongr`.

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
    rcases eq_or_ne c d with rfl | hcd
    · rw [piReflectionPerm_same]
      ext e
      rcases eq_or_ne e c with rfl | he
      · simp [reflection_apply]
      · simp [he]
    · rw [piReflectionPerm_ne P hcd]
      simp [Pi.single_eq_of_ne hcd]
  reflectionPerm_coroot := by
    rintro ⟨c, i⟩ ⟨d, j⟩
    simp only [Function.Embedding.coeFn_mk]
    rcases eq_or_ne c d with rfl | hcd
    · rw [piReflectionPerm_same]
      ext e
      rcases eq_or_ne e c with rfl | he
      · simp [coreflection_apply, root', root_coroot_eq_pairing]
      · simp [he]
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
    rw [Set.image_sigma_eq_iUnion]
    simp [Set.image_image]
  rw [himage, Submodule.span_iUnion_single]
  simp

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

/-- **A finite direct sum is a root system iff every summand is a root system.** -/
theorem isRootSystem_pi_iff : (pi P).IsRootSystem ↔ ∀ c, (P c).IsRootSystem := by
  refine ⟨fun _ c ↦ ⟨eq_top_iff.mpr fun x _ ↦ ?_, eq_top_iff.mpr fun y _ ↦ ?_⟩,
    fun _ ↦ isRootSystem_pi P⟩
  · have hx : Pi.single c x ∈ span R (range (pi P).root) :=
      IsRootSystem.span_root_eq_top (P := pi P) ▸ mem_top
    simpa using (mem_rootSpan_pi_iff P R (Pi.single c x)).mp hx c
  · have hy : Pi.single c y ∈ span R (range (pi P).coroot) :=
      IsRootSystem.span_coroot_eq_top (P := pi P) ▸ mem_top
    simpa using (mem_corootSpan_pi_iff P R (Pi.single c y)).mp hy c

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

/-- **A finite direct sum is `S`-valued iff every summand is `S`-valued.** -/
theorem isValuedIn_pi_iff (S : Type*) [CommRing S] [Algebra S R] :
    (pi P).IsValuedIn S ↔ ∀ c, (P c).IsValuedIn S :=
  ⟨fun _ c ↦
    { exists_value i j := by
        simpa [pi_pairing_same] using (pi P).exists_value (S := S) ⟨c, i⟩ ⟨c, j⟩ },
   fun _ ↦ isValuedIn_pi P S⟩

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
      have ha2 : a * (2 : R) = 0 := by
        have hc : a • (P c).root i = 0 := by simpa [Pi.single_eq_of_ne hcd] using congrFun hab c
        simpa [map_smul, smul_eq_mul, root_coroot'_eq_pairing] using congrArg ((P c).coroot' i) hc
      have hb2 : b * (2 : R) = 0 := by
        have hd : b • (P d).root j = 0 := by
          simpa [Pi.single_eq_of_ne (Ne.symm hcd)] using congrFun hab d
        simpa [map_smul, smul_eq_mul, root_coroot'_eq_pairing] using congrArg ((P d).coroot' j) hd
      exact ⟨h2.right (by simpa using ha2), h2.right (by simpa using hb2)⟩

/-- Every summand of a reduced finite direct sum is reduced. -/
theorem isReduced_of_pi [(pi P).IsReduced] (c : κ) : (P c).IsReduced where
  eq_or_eq_neg i j hdep := by
    have hdep' : ¬ LinearIndependent R ![(pi P).root ⟨c, i⟩, (pi P).root ⟨c, j⟩] := fun hli ↦
      hdep <| by
        refine LinearIndependent.of_comp (LinearMap.single R M c) ?_
        convert hli
        ext k
        fin_cases k <;> rfl
    rcases IsReduced.eq_or_eq_neg (P := pi P) ⟨c, i⟩ ⟨c, j⟩ hdep' with h | h
    · exact Or.inl <| by simpa using congrFun h c
    · exact Or.inr <| by simpa using congrFun h c

/-- **Under regularity of `2`, a finite direct sum is reduced iff every summand is reduced.** -/
theorem isReduced_pi_iff_of_isRegular (h2 : IsRegular (2 : R)) :
    (pi P).IsReduced ↔ ∀ c, (P c).IsReduced :=
  ⟨fun _ c ↦ isReduced_of_pi P c, fun _ ↦ isReduced_pi_of_isRegular P h2⟩

/-- A finite direct sum of reduced root pairings over a ring with no zero divisors (and `2 ≠ 0`) is
reduced. -/
instance isReduced_pi [NoZeroDivisors R] [∀ c, (P c).IsReduced] : (pi P).IsReduced :=
  isReduced_pi_of_isRegular P (IsRegular.of_ne_zero' two_ne_zero)

/-- **Over a ring with no zero divisors (and `2 ≠ 0`), a finite direct sum is reduced iff every
summand is reduced.** -/
theorem isReduced_pi_iff [NoZeroDivisors R] : (pi P).IsReduced ↔ ∀ c, (P c).IsReduced :=
  isReduced_pi_iff_of_isRegular P (IsRegular.of_ne_zero' two_ne_zero)

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
    simp only [LinearEquiv.piCongrLeft_apply_apply, LinearEquiv.piCongrRight_apply,
      LinearEquiv.piCongrLeft_symm_apply]
    exact (e c).toLinearMap_weightEquiv (x c) (y (eκ c))
  root_weightMap := by
    ext ⟨c, i⟩ d
    obtain ⟨c', rfl⟩ := eκ.surjective d
    simp only [comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      _root_.Equiv.sigmaCongr, _root_.Equiv.trans_apply, _root_.Equiv.sigmaCongrRight_apply,
      _root_.Equiv.sigmaCongrLeft_apply, pi_root, LinearEquiv.piCongrLeft_apply_apply,
      LinearEquiv.piCongrRight_apply]
    rcases eq_or_ne c' c with rfl | h
    · simp [Hom.root_weightMap_apply]
    · simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (eκ.injective.ne h)]
  coroot_coweightMap := by
    ext ⟨d, j⟩ c
    obtain ⟨c', rfl⟩ := eκ.surjective d
    have hidx : (_root_.Equiv.sigmaCongr eκ fun c ↦ (e c).indexEquiv).symm ⟨eκ c', j⟩ =
        ⟨c', (e c').indexEquiv.symm j⟩ := by
      rw [_root_.Equiv.symm_apply_eq]
      simp [_root_.Equiv.sigmaCongr]
    simp only [comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      LinearEquiv.piCongrRight_apply, LinearEquiv.piCongrLeft_symm_apply, hidx, pi_coroot]
    rcases eq_or_ne c c' with rfl | h
    · simp [Hom.coroot_coweightMap_apply]
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
  simp [Equiv.piCongr]

@[simp]
theorem Equiv.piCongr_coweightMap_apply (eκ : κ ≃ κ') (e : ∀ c, (P c).Equiv (Q (eκ c)))
    (y : ∀ c, N' c) (c : κ) :
    (Equiv.piCongr eκ e).coweightMap y c = (e c).coweightMap (y (eκ c)) := by
  simp [Equiv.piCongr]

/-- Assembling the identity equivalences along `Equiv.refl κ` gives the identity equivalence of
`RootPairing.pi P`. -/
@[simp]
theorem Equiv.piCongr_id :
    Equiv.piCongr (_root_.Equiv.refl κ) (fun c ↦ Equiv.id (P c)) = Equiv.id (pi P) := by
  refine Equiv.ext (LinearMap.ext fun x ↦ funext fun c ↦ ?_)
    (LinearMap.ext fun y ↦ funext fun c ↦ ?_) (_root_.Equiv.ext fun ⟨c, i⟩ ↦ ?_)
  · exact Equiv.piCongr_weightMap_apply (_root_.Equiv.refl κ) (fun c ↦ Equiv.id (P c)) x c
  · rfl
  · rfl

/-- Composing two `Equiv.piCongr` equivalences gives `Equiv.piCongr` on the composite reindexing
and reindexed composite summand equivalences. -/
@[simp]
theorem Equiv.piCongr_comp
    {κ'' : Type*} [Fintype κ''] [DecidableEq κ'']
    {ι'' M'' N'' : κ'' → Type*}
    [∀ c, AddCommGroup (M'' c)] [∀ c, Module R (M'' c)]
    [∀ c, AddCommGroup (N'' c)] [∀ c, Module R (N'' c)]
    {S : ∀ c, RootPairing (ι'' c) R (M'' c) (N'' c)}
    (eκ : κ ≃ κ') (eκ' : κ' ≃ κ'')
    (e : ∀ c, (P c).Equiv (Q (eκ c)))
    (e' : ∀ c', (Q c').Equiv (S (eκ' c'))) :
    Equiv.comp (Equiv.piCongr eκ' e') (Equiv.piCongr eκ e) =
      Equiv.piCongr (eκ.trans eκ') fun c ↦ Equiv.comp (e' (eκ c)) (e c) := by
  refine Equiv.ext (LinearMap.ext fun x ↦ funext fun c'' ↦ ?_)
    (LinearMap.ext fun y ↦ funext fun c ↦ ?_) (_root_.Equiv.ext fun ⟨c, i⟩ ↦ ?_)
  · obtain ⟨c, rfl⟩ := (eκ.trans eκ').surjective c''
    simp only [Equiv.toHom_comp, Hom.comp, LinearMap.comp_apply, _root_.Equiv.trans_apply]
    rw [Equiv.piCongr_weightMap_apply, Equiv.piCongr_weightMap_apply]
    exact (Equiv.piCongr_weightMap_apply (eκ.trans eκ')
      (fun c ↦ Equiv.comp (e' (eκ c)) (e c)) x c).symm
  · rfl
  · rfl

end Functoriality

end RootPairing
