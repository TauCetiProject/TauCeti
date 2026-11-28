/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DirectSum.Internal
public import TauCeti.LinearAlgebra.RootSystem.Height
import TauCeti.Algebra.Group.Pi.Lemmas
import TauCeti.LinearAlgebra.LinearIndependent.Pi
import TauCeti.LinearAlgebra.Pi

/-!
# Bases and heights for direct sums of root pairings

Bases of the summands of a finite external or internal direct sum of root pairings assemble into a
base of the direct sum (`RootPairing.Base.pi` and `RootPairing.Base.internalDirectSum`), and every
base of a direct sum restricts back to bases of the summands (`RootPairing.Base.restrictPi` and
`RootPairing.Base.restrictInternalDirectSum`).

Heights and positivity of roots match those in their own summands, and direct-sum congruences carry
assembled bases to assembled bases.

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

private theorem coe_sigma_preimage_eq {κ : Type*} {ι : κ → Type*} (t : Finset (Σ c, ι c)) :
    (Set.univ.sigma fun d ↦
        ((t.preimage (Sigma.mk d) sigma_mk_injective.injOn : Finset (ι d)) : Set (ι d))) =
      (t : Set (Σ d, ι d)) := by
  simp only [Finset.coe_preimage, Set.univ_sigma_preimage_mk]

private theorem linearIndepOn_pi_single_of_eq {κ R : Type*} [Fintype κ] [DecidableEq κ] [CommRing R]
    {ι M : κ → Type*} [∀ c, AddCommGroup (M c)] [∀ c, Module R (M c)]
    {w : (Σ c, ι c) → ∀ c, M c} {v : ∀ c, ι c → M c}
    (hw : ∀ c i, w ⟨c, i⟩ = Pi.single c (v c i)) {s : ∀ c, Finset (ι c)}
    (hv : ∀ c, LinearIndepOn R (v c) (s c : Set (ι c))) :
    LinearIndepOn R w ((Finset.univ.sigma s : Finset (Σ c, ι c)) : Set (Σ c, ι c)) := by
  have hfn : w = fun p : Σ c, ι c ↦ Pi.single p.1 (v p.1 p.2) := funext fun ⟨c, i⟩ ↦ hw c i
  rw [hfn, Finset.coe_sigma, Finset.coe_univ]
  exact (Pi.linearIndepOn_single_iff v).mpr fun c _ ↦ hv c

private theorem linearIndepOn_restrictPi_of_eq {κ R : Type*} [DecidableEq κ] [CommRing R]
    {ι M : κ → Type*} [∀ c, AddCommGroup (M c)] [∀ c, Module R (M c)]
    {w : (Σ c, ι c) → ∀ c, M c} {v : ∀ c, ι c → M c}
    (hw : ∀ c i, w ⟨c, i⟩ = Pi.single c (v c i)) {t : Finset (Σ c, ι c)}
    (ht : LinearIndepOn R w (t : Set (Σ c, ι c))) (c : κ) :
    LinearIndepOn R (v c)
      ((t.preimage (Sigma.mk c) sigma_mk_injective.injOn : Finset (ι c)) : Set (ι c)) := by
  have hfn : (fun p : Σ d, ι d ↦ Pi.single p.1 (v p.1 p.2)) = w :=
    funext fun ⟨d, i⟩ ↦ (hw d i).symm
  rw [← coe_sigma_preimage_eq t] at ht
  exact (Pi.linearIndepOn_single_iff v).mp (by rwa [hfn]) c (Set.mem_univ c)

private theorem pi_single_mem_closure_or_neg_mem_sigma_iff {κ : Type*} [DecidableEq κ]
    {ι M : κ → Type*} [∀ c, AddCommGroup (M c)]
    {w : (Σ c, ι c) → ∀ c, M c} {v : ∀ c, ι c → M c}
    (hw : ∀ c i, w ⟨c, i⟩ = Pi.single c (v c i)) (s : ∀ c, Set (ι c)) (c : κ) (i : ι c) :
    w ⟨c, i⟩ ∈ AddSubmonoid.closure (w '' (Set.univ.sigma s)) ∨
        -w ⟨c, i⟩ ∈ AddSubmonoid.closure (w '' (Set.univ.sigma s)) ↔
      v c i ∈ AddSubmonoid.closure (v c '' s c) ∨
        -v c i ∈ AddSubmonoid.closure (v c '' s c) := by
  have hfn : w = fun p : Σ d, ι d ↦ Pi.single p.1 (v p.1 p.2) := funext fun ⟨d, j⟩ ↦ hw d j
  rw [hfn, Pi.image_sigma_single]
  simp [← Pi.single_neg]

/-- **The base of a finite direct sum of root pairings** assembled from bases of its summands.
Its simple-root support is the disjoint union `Finset.univ.sigma fun c ↦ (b c).support`. -/
noncomputable def Base.pi {P : ∀ c, RootPairing (ι c) R (M c) (N c)} (b : ∀ c, (P c).Base) :
    (RootPairing.pi P).Base where
  support := Finset.univ.sigma fun c ↦ (b c).support
  linearIndepOn_root := linearIndepOn_pi_single_of_eq (pi_root P) fun c ↦ (b c).linearIndepOn_root
  linearIndepOn_coroot :=
    linearIndepOn_pi_single_of_eq (pi_coroot P) fun c ↦ (b c).linearIndepOn_coroot
  root_mem_or_neg_mem p := by
    rw [Finset.coe_sigma, Finset.coe_univ]
    exact (pi_single_mem_closure_or_neg_mem_sigma_iff (pi_root P) _ p.1 p.2).mpr
      ((b p.1).root_mem_or_neg_mem p.2)
  coroot_mem_or_neg_mem p := by
    rw [Finset.coe_sigma, Finset.coe_univ]
    exact (pi_single_mem_closure_or_neg_mem_sigma_iff (pi_coroot P) _ p.1 p.2).mpr
      ((b p.1).coroot_mem_or_neg_mem p.2)

variable {P}

@[simp]
theorem Base.support_pi (b : ∀ c, (P c).Base) :
    (Base.pi b).support = Finset.univ.sigma fun c ↦ (b c).support :=
  (rfl)

/-- **Restricting a base of `RootPairing.pi P` to a summand** by taking the simple roots lying in
that summand. -/
noncomputable def Base.restrictPi (b : (RootPairing.pi P).Base) (c : κ) : (P c).Base where
  support := b.support.preimage (Sigma.mk c) sigma_mk_injective.injOn
  linearIndepOn_root := linearIndepOn_restrictPi_of_eq (pi_root P) b.linearIndepOn_root c
  linearIndepOn_coroot := linearIndepOn_restrictPi_of_eq (pi_coroot P) b.linearIndepOn_coroot c
  root_mem_or_neg_mem i :=
    (pi_single_mem_closure_or_neg_mem_sigma_iff (pi_root P)
      (fun d ↦ (b.support.preimage (Sigma.mk d) sigma_mk_injective.injOn : Finset (ι d))) c i).mp <|
      by rw [coe_sigma_preimage_eq]; exact b.root_mem_or_neg_mem ⟨c, i⟩
  coroot_mem_or_neg_mem i :=
    (pi_single_mem_closure_or_neg_mem_sigma_iff (pi_coroot P)
      (fun d ↦ (b.support.preimage (Sigma.mk d) sigma_mk_injective.injOn : Finset (ι d))) c i).mp <|
      by rw [coe_sigma_preimage_eq]; exact b.coroot_mem_or_neg_mem ⟨c, i⟩

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

/-- The height of a root in a finite direct sum is its height in its own summand. -/
@[simp]
theorem Base.height_pi [CharZero R] (b : ∀ c, (P c).Base) (c : κ) (i : ι c) :
    (Base.pi b).height ⟨c, i⟩ = (b c).height i := by
  obtain ⟨f, -, -, hf⟩ := (b c).exists_root_eq_sum_int i
  let g : (Σ d, ι d) → ℤ := fun p ↦ if h : p.1 = c then f (h ▸ p.2) else 0
  have hg : (RootPairing.pi P).root ⟨c, i⟩ =
      ∑ p ∈ (Base.pi b).support, g p • (RootPairing.pi P).root p := by
    simp only [Base.support_pi, Finset.sum_sigma, g, pi_root, dite_smul, zero_smul,
      Finset.sum_dite_irrel, Finset.sum_const_zero, Finset.sum_dite_eq', Finset.mem_univ,
      ↓reduceIte, hf]
    rw [← LinearMap.single_apply (R := R) (φ := M), map_sum]
    simp [map_zsmul]
  rw [(Base.pi b).height_eq_sum hg, (b c).height_eq_sum hf]
  simp [g, Finset.sum_sigma, Finset.sum_dite_irrel, Finset.sum_const_zero, Finset.sum_dite_eq']

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
  ext p
  obtain ⟨⟨c, i⟩, rfl⟩ := (Equiv.piCongr eκ e).indexEquiv.surjective p
  rw [Base.mem_support_map_iff, _root_.Equiv.symm_apply_apply]
  simp only [Base.support_pi, Finset.mem_sigma, Finset.mem_univ, true_and,
    Equiv.piCongr_indexEquiv, ← hb c, Base.mem_support_map_iff, _root_.Equiv.symm_apply_apply]

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
