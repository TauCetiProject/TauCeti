/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import TauCeti.LinearAlgebra.RootSystem.DirectSum.Internal
public import TauCeti.LinearAlgebra.RootSystem.Height
import TauCeti.LinearAlgebra.LinearIndependent.Pi

/-!
# Bases, Cartan matrices, and heights for direct sums of root pairings

Bases of the summands of a finite external or internal direct sum of root pairings assemble into a
base of the direct sum (`RootPairing.Base.pi` and `RootPairing.Base.internalDirectSum`), and every
base of a direct sum restricts back to bases of the summands (`RootPairing.Base.restrictPi` and
`RootPairing.Base.restrictInternalDirectSum`).

Cartan matrices decompose block-diagonally across summands, heights and positivity of roots match
those in their own summands, and direct-sum congruences carry assembled bases to assembled bases.

## Main definitions

* `RootPairing.Base.pi`, `RootPairing.Base.restrictPi`: assembly and restriction of bases for
  finite external direct sums.
* `RootPairing.Base.internalDirectSum`, `RootPairing.Base.restrictInternalDirectSum`: assembly and
  restriction of bases for finite internal direct sums.

## Main results

* `RootPairing.Base.pi_restrictPi`, `RootPairing.Base.restrictPi_pi`,
  `RootPairing.Base.internalDirectSum_restrictInternalDirectSum`,
  `RootPairing.Base.restrictInternalDirectSum_internalDirectSum`: mutual inverse laws for
  assembling and restricting bases.
* `RootPairing.Base.cartanMatrixIn_pi_same`, `RootPairing.Base.cartanMatrixIn_pi_ne`,
  `RootPairing.Base.cartanMatrixIn_internalDirectSum_same`,
  `RootPairing.Base.cartanMatrixIn_internalDirectSum_ne`: block-diagonal decomposition of Cartan
  matrices.
* `RootPairing.Base.height_pi`, `RootPairing.Base.isPos_pi_iff`,
  `RootPairing.Base.height_internalDirectSum`, `RootPairing.Base.isPos_internalDirectSum_iff`:
  heights and positivity on direct sums.
* `RootPairing.Base.map_piCongr_pi`, `RootPairing.Base.map_piCongr_refl_pi`,
  `RootPairing.Base.map_internalDirectSumCongr`,
  `RootPairing.Base.map_internalDirectSumCongr_refl`: compatibility of base assembly with
  direct-sum congruences.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §1, no. 2.
-/

public section

open Function Set Submodule TauCeti

namespace RootPairing

section External

variable {κ R : Type*} [Fintype κ] [DecidableEq κ] [CommRing R] [NeZero (2 : R)]
  {ι M N : κ → Type*}
  [∀ c, AddCommGroup (M c)] [∀ c, Module R (M c)]
  [∀ c, AddCommGroup (N c)] [∀ c, Module R (N c)]
  (P : ∀ c, RootPairing (ι c) R (M c) (N c))

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
noncomputable def Base.restrictPi (b : (RootPairing.pi P).Base) (c : κ) : (P c).Base :=
  have hsupp : (b.support : Set (Σ d, ι d)) = Set.univ.sigma fun d ↦
      ((b.support.preimage (Sigma.mk d) sigma_mk_injective.injOn : Finset (ι d)) : Set (ι d)) := by
    simp only [Finset.coe_preimage, Set.univ_sigma_preimage_mk]
  { support := b.support.preimage (Sigma.mk c) sigma_mk_injective.injOn
    linearIndepOn_root := by
      have hfn : (fun p : Σ d, ι d ↦ Pi.single p.1 ((P p.1).root p.2)) =
          (RootPairing.pi P).root :=
        funext fun ⟨d, i⟩ ↦ (pi_root P d i).symm
      have hroot : LinearIndepOn R (fun p : Σ d, ι d ↦ Pi.single p.1 ((P p.1).root p.2))
          (Set.univ.sigma fun d ↦ ((b.support.preimage (Sigma.mk d)
            sigma_mk_injective.injOn : Finset (ι d)) : Set (ι d))) := by
        rw [hfn, ← hsupp]
        exact b.linearIndepOn_root
      exact (Pi.linearIndepOn_single_iff fun d ↦ (P d).root).mp hroot c (Set.mem_univ c)
    linearIndepOn_coroot := by
      have hfn : (fun p : Σ d, ι d ↦ Pi.single p.1 ((P p.1).coroot p.2)) =
          (RootPairing.pi P).coroot :=
        funext fun ⟨d, i⟩ ↦ (pi_coroot P d i).symm
      have hcoroot : LinearIndepOn R (fun p : Σ d, ι d ↦ Pi.single p.1 ((P p.1).coroot p.2))
          (Set.univ.sigma fun d ↦ ((b.support.preimage (Sigma.mk d)
            sigma_mk_injective.injOn : Finset (ι d)) : Set (ι d))) := by
        rw [hfn, ← hsupp]
        exact b.linearIndepOn_coroot
      exact (Pi.linearIndepOn_single_iff fun d ↦ (P d).coroot).mp hcoroot c (Set.mem_univ c)
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
          simpa using hle (AddSubmonoid.mem_map_of_mem (Pi.evalAddMonoidHom N c) h) }

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

end External

section Internal

variable {κ R M : Type*} [Finite κ] [CommRing R] [NeZero (2 : R)]
  [AddCommGroup M] [Module R M]
  {E : κ → Submodule R M} {hEi : iSupIndep E} {hEt : ⨆ c, E c = ⊤}
  {ι N : κ → Type*} [∀ c, AddCommGroup (N c)] [∀ c, Module R (N c)]
  {P : ∀ c, RootPairing (ι c) R (E c) (N c)}

/-- **The base of a finite internal direct sum** assembled from bases of its summands. -/
noncomputable def Base.internalDirectSum {P : ∀ c, RootPairing (ι c) R (E c) (N c)}
    (hEi : iSupIndep E) (hEt : ⨆ c, E c = ⊤) (b : ∀ c, (P c).Base) :
    (RootPairing.internalDirectSum hEi hEt P).Base :=
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  (Base.pi b).map (piEquivInternalDirectSum hEi hEt P)

@[simp]
theorem Base.mem_support_internalDirectSum (b : ∀ c, (P c).Base) (s : Σ c, ι c) :
    s ∈ (Base.internalDirectSum hEi hEt b).support ↔ s.2 ∈ (b s.1).support := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  simp [Base.internalDirectSum, Base.map]

/-- **Restricting a base of `RootPairing.internalDirectSum hEi hEt P` to a summand** by taking
the simple roots lying in that summand. -/
noncomputable def Base.restrictInternalDirectSum
    (b : (RootPairing.internalDirectSum hEi hEt P).Base) (c : κ) : (P c).Base :=
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  (b.map (piEquivInternalDirectSum hEi hEt P).symm).restrictPi c

@[simp]
theorem Base.mem_support_restrictInternalDirectSum
    (b : (RootPairing.internalDirectSum hEi hEt P).Base) (c : κ) (i : ι c) :
    i ∈ (b.restrictInternalDirectSum c).support ↔ ⟨c, i⟩ ∈ b.support := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  simp [Base.restrictInternalDirectSum, Base.map]

/-- Assembling the restrictions of a base of `internalDirectSum` recovers the original base. -/
@[simp]
theorem Base.internalDirectSum_restrictInternalDirectSum
    (b : (RootPairing.internalDirectSum hEi hEt P).Base) :
    Base.internalDirectSum hEi hEt (fun c ↦ b.restrictInternalDirectSum c) = b := by
  ext ⟨c, i⟩
  simp

/-- Restricting an assembled base `Base.internalDirectSum hEi hEt b` to coordinate `c` recovers
`b c`. -/
@[simp]
theorem Base.restrictInternalDirectSum_internalDirectSum (b : ∀ c, (P c).Base) (c : κ) :
    (Base.internalDirectSum hEi hEt b).restrictInternalDirectSum c = b c := by
  ext i
  simp

@[simp]
theorem Base.cartanMatrixIn_internalDirectSum_same (S : Type*) [CommRing S] [Algebra S R]
    [FaithfulSMul S R] [∀ c, (P c).IsValuedIn S] (b : ∀ c, (P c).Base) (c : κ)
    (i j : (b c).support) :
    (Base.internalDirectSum hEi hEt b).cartanMatrixIn S
        ⟨⟨c, i.val⟩, by simp [i.property]⟩ ⟨⟨c, j.val⟩, by simp [j.property]⟩ =
      (b c).cartanMatrixIn S i j := by
  simp [Base.cartanMatrixIn_def]

@[simp]
theorem Base.cartanMatrixIn_internalDirectSum_ne (S : Type*) [CommRing S] [Algebra S R]
    [FaithfulSMul S R] [∀ c, (P c).IsValuedIn S] (b : ∀ c, (P c).Base) {c d : κ} (hcd : c ≠ d)
    (i : (b c).support) (j : (b d).support) :
    (Base.internalDirectSum hEi hEt b).cartanMatrixIn S
        ⟨⟨c, i.val⟩, by simp [i.property]⟩ ⟨⟨d, j.val⟩, by simp [j.property]⟩ = 0 := by
  simp [Base.cartanMatrixIn_def, internalDirectSum_pairingIn_ne hEi hEt P S hcd]

/-- The height of a root in a finite internal direct sum is its height in its own summand. -/
@[simp]
theorem Base.height_internalDirectSum [CharZero R] (b : ∀ c, (P c).Base) (c : κ) (i : ι c) :
    (Base.internalDirectSum hEi hEt b).height ⟨c, i⟩ = (b c).height i := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  dsimp only [Base.internalDirectSum]
  rw [← piEquivInternalDirectSum_indexEquiv hEi hEt P ⟨c, i⟩, Base.height_map, Base.height_pi]

/-- A root of an internal direct sum is positive for `Base.internalDirectSum` iff it is positive in
its summand. -/
@[simp]
theorem Base.isPos_internalDirectSum_iff [CharZero R] (b : ∀ c, (P c).Base) (c : κ) (i : ι c) :
    (Base.internalDirectSum hEi hEt b).IsPos ⟨c, i⟩ ↔ (b c).IsPos i := by
  simp [Base.isPos_iff]

theorem Base.support_internalDirectSum [Fintype κ] {hEi : iSupIndep E} {hEt : ⨆ c, E c = ⊤}
    {P : ∀ c, RootPairing (ι c) R (E c) (N c)} (b : ∀ c, (P c).Base) :
    (Base.internalDirectSum hEi hEt b).support = Finset.univ.sigma fun c ↦ (b c).support := by
  ext ⟨c, i⟩
  simp

end Internal

section Functoriality

section External

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

end External

section Internal

variable {κ κ' R M M' : Type*} [Finite κ] [Finite κ'] [CommRing R] [NeZero (2 : R)]
  [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  {E : κ → Submodule R M} {E' : κ' → Submodule R M'}
  {ι N : κ → Type*} [∀ c, AddCommGroup (N c)] [∀ c, Module R (N c)]
  {ι' N' : κ' → Type*} [∀ c', AddCommGroup (N' c')] [∀ c', Module R (N' c')]
  {P : ∀ c, RootPairing (ι c) R (E c) (N c)}
  {Q : ∀ c', RootPairing (ι' c') R (E' c') (N' c')}

/-- Mapping an assembled base `Base.internalDirectSum hEi hEt b` along
`Equiv.internalDirectSumCongr` produces `Base.internalDirectSum hEi' hEt' b'` whenever `e c`
carries `b c` to `b' (eκ c)`. -/
theorem Base.map_internalDirectSumCongr
    (hEi : iSupIndep E) (hEt : ⨆ c, E c = ⊤)
    (hEi' : iSupIndep E') (hEt' : ⨆ c', E' c' = ⊤)
    (eκ : κ ≃ κ') (e : ∀ c, (P c).Equiv (Q (eκ c)))
    {b : ∀ c, (P c).Base} {b' : ∀ c', (Q c').Base}
    (hb : ∀ c, (b c).map (e c) = b' (eκ c)) :
    (Base.internalDirectSum hEi hEt b).map
        (Equiv.internalDirectSumCongr hEi hEt hEi' hEt' eκ e) =
      Base.internalDirectSum hEi' hEt' b' := by
  classical
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : Fintype κ' := Fintype.ofFinite κ'
  dsimp only [Base.internalDirectSum]
  rw [← Base.map_piCongr_pi eκ e hb, Base.ext_iff]
  simp only [Base.support_map_eq, Finset.image_image]
  refine Finset.image_congr fun ⟨c, i⟩ _ ↦ ?_
  simp

/-- Mapping an assembled base `Base.internalDirectSum hEi hEt b` along
`Equiv.internalDirectSumCongr hEi hEt hEi' hEt' (.refl κ) e` assembles the transported summand
bases. -/
@[simp]
theorem Base.map_internalDirectSumCongr_refl
    {E'' : κ → Submodule R M'}
    {ι'' N'' : κ → Type*} [∀ c, AddCommGroup (N'' c)] [∀ c, Module R (N'' c)]
    {Q : ∀ c, RootPairing (ι'' c) R (E'' c) (N'' c)}
    (hEi : iSupIndep E) (hEt : ⨆ c, E c = ⊤)
    (hEi' : iSupIndep E'') (hEt' : ⨆ c, E'' c = ⊤)
    (e : ∀ c, (P c).Equiv (Q c)) (b : ∀ c, (P c).Base) :
    (Base.internalDirectSum hEi hEt b).map
        (Equiv.internalDirectSumCongr hEi hEt hEi' hEt' (_root_.Equiv.refl κ) e) =
      Base.internalDirectSum hEi' hEt' fun c ↦ (b c).map (e c) :=
  Base.map_internalDirectSumCongr hEi hEt hEi' hEt' (_root_.Equiv.refl κ) e fun _ ↦ rfl

end Internal

end Functoriality

end RootPairing
