/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.FSymbols.Basic

/-!
# Relabeling and base change for F-symbols and R-symbols

This file constructs pushforward (`reindex`) of `TauCeti.FusionRules` along arbitrary bijections
`σ : ι ≃ ι'`, together with relabeling (`reindex`) along unit- and multiplicity-preserving
bijections and base change (`map`) along ring homomorphisms for `TauCeti.FSymbols` and
`TauCeti.RSymbols`.

Because the pentagon, triangle, hexagon, and two-sided matrix inverse conditions are polynomial
identities in the matrix entries, entrywise application of any ring homomorphism `f : R →+* S`
transports F-symbols and R-symbols from `R` to `S`, and any bijection intertwining the unit and
multiplicities transports them covariantly. For `FSymbols`, this satisfies
`reindex (Equiv.refl ι) = id`, `reindex (σ.trans τ) = reindex τ ∘ reindex σ`,
`map (RingHom.id R) = id`, `map (g.comp f) = map g ∘ map f`, and commutativity of `reindex` with
`map`; for `RSymbols P`, whose type depends on `P`, the corresponding identities hold up to
`RSymbols.cast` (`cast_reindex_refl`, `cast_reindex_trans`, `cast_map_id`, `cast_map_comp`,
`cast_reindex_map`).

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*][egno15], §4.9–4.10.
* A. Kitaev, *Anyons in an exactly solved model and beyond*, Ann. Physics **321** (2006),
  Appendix E, §E.1 and §E.3.
-/

public section

namespace TauCeti

universe u u' u'' v v' v''

/-! ### Relabeling of fusion rules -/

namespace FusionRules

section Reindex

variable {ι : Type u} {ι' : Type u'} {ι'' : Type u''}
  [DecidableEq ι] [DecidableEq ι'] [DecidableEq ι'']

/-- Push `FusionRules` forward along a bijection `σ : ι ≃ ι'`. -/
def reindex (σ : ι ≃ ι') (N : FusionRules ι) : FusionRules ι' where
  unit := σ N.unit
  N a' b' c' := N.N (σ.symm a') (σ.symm b') (σ.symm c')
  N_unit_left _ _ := by simp [N.N_unit_left, σ.symm.injective.eq_iff]
  N_unit_right _ _ := by simp [N.N_unit_right, σ.symm.injective.eq_iff]

@[simp] theorem reindex_unit (σ : ι ≃ ι') (N : FusionRules ι) : (N.reindex σ).unit = σ N.unit :=
  (rfl)
@[simp] theorem reindex_N_apply (σ : ι ≃ ι') (N : FusionRules ι) (a' b' c' : ι') :
    (N.reindex σ).N a' b' c' = N.N (σ.symm a') (σ.symm b') (σ.symm c') := (rfl)
theorem N_eq_reindex_N (σ : ι ≃ ι') (N : FusionRules ι) (a b c : ι) :
    N.N a b c = (N.reindex σ).N (σ a) (σ b) (σ c) := by simp

@[simp] theorem reindex_refl_apply (N : FusionRules ι) : N.reindex (Equiv.refl ι) = N := by
  ext <;> rfl
theorem reindex_refl : (FusionRules.reindex (Equiv.refl ι) : FusionRules ι → FusionRules ι) = id :=
  funext reindex_refl_apply

@[simp] theorem reindex_trans_apply (σ : ι ≃ ι') (τ : ι' ≃ ι'') (N : FusionRules ι) :
    (N.reindex σ).reindex τ = N.reindex (σ.trans τ) := by ext <;> rfl
theorem reindex_trans (σ : ι ≃ ι') (τ : ι' ≃ ι'') :
    (FusionRules.reindex (σ.trans τ) : FusionRules ι → FusionRules ι'') =
      FusionRules.reindex τ ∘ FusionRules.reindex σ :=
  funext fun N ↦ (reindex_trans_apply σ τ N).symm

/-- `FusionRules.reindex` along a bijection `σ : ι ≃ ι'` as an equivalence of types. -/
def reindexEquiv (σ : ι ≃ ι') : FusionRules ι ≃ FusionRules ι' where
  toFun := reindex σ
  invFun := reindex σ.symm
  left_inv _ := by simp
  right_inv _ := by simp

@[simp] theorem reindexEquiv_apply (σ : ι ≃ ι') (N : FusionRules ι) :
    reindexEquiv σ N = N.reindex σ := (rfl)
@[simp] theorem reindexEquiv_symm (σ : ι ≃ ι') : (reindexEquiv σ).symm = reindexEquiv σ.symm :=
  (rfl)

section IndexEquiv

variable {N : FusionRules ι} {N' : FusionRules ι'}

theorem N_eq_N_symm (σ : ι ≃ ι') (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c))
    (a' b' c' : ι') : N'.N a' b' c' = N.N (σ.symm a') (σ.symm b') (σ.symm c') := by
  simpa using (hN (σ.symm a') (σ.symm b') (σ.symm c')).symm

variable (σ : ι ≃ ι') (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c))

/-- Equivalence between `N'.Left a' b' c' d'` and
`N.Left (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d')`. -/
def leftSymmEquiv (a' b' c' d' : ι') :
    N'.Left a' b' c' d' ≃ N.Left (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d') :=
  Equiv.sigmaCongr σ.symm fun e' ↦
    (finCongr (N_eq_N_symm σ hN a' b' e')).prodCongr (finCongr (N_eq_N_symm σ hN e' c' d'))

@[simp] theorem leftSymmEquiv_apply (a' b' c' d' : ι') (x : N'.Left a' b' c' d') :
    leftSymmEquiv σ hN a' b' c' d' x = ⟨σ.symm x.1, x.2.1.cast (N_eq_N_symm σ hN a' b' x.1),
      x.2.2.cast (N_eq_N_symm σ hN x.1 c' d')⟩ := by
  rcases x with ⟨_, _, _⟩; simp [leftSymmEquiv, Equiv.sigmaCongr]

@[simp] theorem leftSymmEquiv_symm_apply (a' b' c' d' : ι')
    (x : N.Left (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d')) :
    (leftSymmEquiv σ hN a' b' c' d').symm x =
      ⟨σ x.1, x.2.1.cast (by simp [hN]), x.2.2.cast (by simp [hN])⟩ := by
  rcases x with ⟨_, _, _⟩; rw [(leftSymmEquiv σ hN a' b' c' d').symm_apply_eq, leftSymmEquiv_apply]
  exact Left.ext (by simp) rfl rfl

/-- Equivalence between `N'.Right a' b' c' d'` and
`N.Right (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d')`. -/
def rightSymmEquiv (a' b' c' d' : ι') :
    N'.Right a' b' c' d' ≃ N.Right (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d') :=
  Equiv.sigmaCongr σ.symm fun f' ↦
    (finCongr (N_eq_N_symm σ hN b' c' f')).prodCongr (finCongr (N_eq_N_symm σ hN a' f' d'))

@[simp] theorem rightSymmEquiv_apply (a' b' c' d' : ι') (y : N'.Right a' b' c' d') :
    rightSymmEquiv σ hN a' b' c' d' y = ⟨σ.symm y.1, y.2.1.cast (N_eq_N_symm σ hN b' c' y.1),
      y.2.2.cast (N_eq_N_symm σ hN a' y.1 d')⟩ := by
  rcases y with ⟨_, _, _⟩; simp [rightSymmEquiv, Equiv.sigmaCongr]

@[simp] theorem rightSymmEquiv_symm_apply (a' b' c' d' : ι')
    (y : N.Right (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d')) :
    (rightSymmEquiv σ hN a' b' c' d').symm y =
      ⟨σ y.1, y.2.1.cast (by simp [hN]), y.2.2.cast (by simp [hN])⟩ := by
  rcases y with ⟨_, _, _⟩
  rw [(rightSymmEquiv σ hN a' b' c' d').symm_apply_eq, rightSymmEquiv_apply]
  exact Right.ext (by simp) rfl rfl

end IndexEquiv

end Reindex

end FusionRules

/-! ### Relabeling and base change for F-symbols -/

namespace FSymbols

section ReindexAndMap

open FusionRules (N_eq_N_symm leftSymmEquiv rightSymmEquiv leftSymmEquiv_apply rightSymmEquiv_apply)

variable {R : Type v} {S : Type v'} {T : Type v''} [CommRing R] [CommRing S] [CommRing T]
  {ι : Type u} {ι' : Type u'} {ι'' : Type u''}
  [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype ι''] [DecidableEq ι'']
  {N : FusionRules ι} {N' : FusionRules ι'} {N'' : FusionRules ι''}

private theorem triangle_of_eq_unit (P : FSymbols R N) {u₀ : ι} (hu : u₀ = N.unit)
    (a c d : ι) (ua : Fin (N.N a u₀ a)) (uc : Fin (N.N u₀ c c)) (i j : Fin (N.N a c d)) :
    P.F a u₀ c d ⟨a, ua, i⟩ ⟨c, uc, j⟩ = if i = j then 1 else 0 := by
  subst hu; rw [N.fin_unit_right_eq a ua, N.fin_unit_left_eq c uc]; exact P.triangle a c d i j

private theorem F_cast_of_eq (P : FSymbols R N) {a₁ a b₁ b c₁ c d₁ d e₁ e f₁ f : ι}
    (ha : a₁ = a) (hb : b₁ = b) (hc : c₁ = c) (hd : d₁ = d) (he : e₁ = e) (hf : f₁ = f)
    {i₁ : Fin (N.N a₁ b₁ e₁)} {i : Fin (N.N a b e)} (hi : i₁.val = i.val)
    {j₁ : Fin (N.N e₁ c₁ d₁)} {j : Fin (N.N e c d)} (hj : j₁.val = j.val)
    {k₁ : Fin (N.N b₁ c₁ f₁)} {k : Fin (N.N b c f)} (hk : k₁.val = k.val)
    {l₁ : Fin (N.N a₁ f₁ d₁)} {l : Fin (N.N a f d)} (hl : l₁.val = l.val) :
    P.F a₁ b₁ c₁ d₁ ⟨e₁, i₁, j₁⟩ ⟨f₁, k₁, l₁⟩ = P.F a b c d ⟨e, i, j⟩ ⟨f, k, l⟩ := by
  subst ha; subst hb; subst hc; subst hd; subst he; subst hf
  rw [Fin.ext hi, Fin.ext hj, Fin.ext hk, Fin.ext hl]

/-- Transport `FSymbols` covariantly along a unit- and multiplicity-preserving bijection
`σ : ι ≃ ι'`. -/
def reindex (σ : ι ≃ ι') (hu : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) (P : FSymbols R N) : FSymbols R N' where
  F a' b' c' d' := (P.F (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d')).submatrix
    (leftSymmEquiv σ hN a' b' c' d') (rightSymmEquiv σ hN a' b' c' d')
  Finv a' b' c' d' := (P.Finv (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d')).submatrix
    (rightSymmEquiv σ hN a' b' c' d') (leftSymmEquiv σ hN a' b' c' d')
  F_mul_Finv _ _ _ _ := by rw [Matrix.submatrix_mul_equiv, P.F_mul_Finv, Matrix.submatrix_one_equiv]
  Finv_mul_F _ _ _ _ := by rw [Matrix.submatrix_mul_equiv, P.Finv_mul_F, Matrix.submatrix_one_equiv]
  pentagon A' B' C' D' E' p' q' r' s' i₁' i₂' i₃' k' m' n' := by
    refine Eq.trans ?_ ((P.pentagon
      (σ.symm A') (σ.symm B') (σ.symm C') (σ.symm D') (σ.symm E')
      (σ.symm p') (σ.symm q') (σ.symm r') (σ.symm s')
      (i₁'.cast (N_eq_N_symm σ hN A' B' p')) (i₂'.cast (N_eq_N_symm σ hN p' C' q'))
      (i₃'.cast (N_eq_N_symm σ hN q' D' E')) (k'.cast (N_eq_N_symm σ hN C' D' r'))
      (m'.cast (N_eq_N_symm σ hN B' r' s')) (n'.cast (N_eq_N_symm σ hN A' s' E'))).trans
        (Eq.symm ?_))
    · exact Fintype.sum_equiv (finCongr (N_eq_N_symm σ hN p' r' E')) _ _ fun _ ↦ by simp
    · exact Fintype.sum_equiv σ.symm _ _ fun t' ↦
        Fintype.sum_equiv (finCongr (N_eq_N_symm σ hN B' C' t')) _ _ fun _ ↦
          Fintype.sum_equiv (finCongr (N_eq_N_symm σ hN A' t' q')) _ _ fun _ ↦
            Fintype.sum_equiv (finCongr (N_eq_N_symm σ hN t' D' s')) _ _ fun _ ↦ by simp
  triangle a' c' d' i' j' := by
    simpa [Fin.ext_iff] using P.triangle_of_eq_unit (by rw [← hu, σ.symm_apply_apply])
      (σ.symm a') (σ.symm c') (σ.symm d')
      ((N'.unitRight a').cast (N_eq_N_symm σ hN a' N'.unit a'))
      ((N'.unitLeft c').cast (N_eq_N_symm σ hN N'.unit c' c'))
      (i'.cast (N_eq_N_symm σ hN a' c' d')) (j'.cast (N_eq_N_symm σ hN a' c' d'))

section ReindexLemmas

variable (σ : ι ≃ ι') (hu : σ N.unit = N'.unit) (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c))

@[simp] theorem reindex_F_apply (P : FSymbols R N) (a' b' c' d' : ι') (x : N'.Left a' b' c' d')
    (y : N'.Right a' b' c' d') : (P.reindex σ hu hN).F a' b' c' d' x y =
      P.F (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d')
        (leftSymmEquiv σ hN a' b' c' d' x) (rightSymmEquiv σ hN a' b' c' d' y) := (rfl)

@[simp] theorem reindex_Finv_apply (P : FSymbols R N) (a' b' c' d' : ι') (y : N'.Right a' b' c' d')
    (x : N'.Left a' b' c' d') : (P.reindex σ hu hN).Finv a' b' c' d' y x =
      P.Finv (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d')
        (rightSymmEquiv σ hN a' b' c' d' y) (leftSymmEquiv σ hN a' b' c' d' x) := (rfl)

theorem reindex_F (P : FSymbols R N) (a' b' c' d' : ι') : (P.reindex σ hu hN).F a' b' c' d' =
    (P.F (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d')).submatrix
      (leftSymmEquiv σ hN a' b' c' d') (rightSymmEquiv σ hN a' b' c' d') := (rfl)

theorem reindex_Finv (P : FSymbols R N) (a' b' c' d' : ι') : (P.reindex σ hu hN).Finv a' b' c' d' =
    (P.Finv (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d')).submatrix
      (rightSymmEquiv σ hN a' b' c' d') (leftSymmEquiv σ hN a' b' c' d') := (rfl)

end ReindexLemmas

@[simp] theorem reindex_refl_apply (hu : Equiv.refl ι N.unit = N.unit)
    (hN : ∀ a b c, N.N a b c = N.N (Equiv.refl ι a) (Equiv.refl ι b) (Equiv.refl ι c))
    (P : FSymbols R N) : P.reindex (Equiv.refl ι) hu hN = P := by
  ext a b c d ⟨e, i, j⟩ ⟨f, k, l⟩
  rw [reindex_F_apply, leftSymmEquiv_apply, rightSymmEquiv_apply]
  exact F_cast_of_eq P rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem reindex_refl (hu : Equiv.refl ι N.unit = N.unit)
    (hN : ∀ a b c, N.N a b c = N.N (Equiv.refl ι a) (Equiv.refl ι b) (Equiv.refl ι c)) :
    (FSymbols.reindex (Equiv.refl ι) hu hN : FSymbols R N → FSymbols R N) = id :=
  funext (reindex_refl_apply hu hN)

@[simp] theorem reindex_trans_apply (σ : ι ≃ ι') (τ : ι' ≃ ι'') (hu₁ : σ N.unit = N'.unit)
    (hN₁ : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) (hu₂ : τ N'.unit = N''.unit)
    (hN₂ : ∀ a' b' c', N'.N a' b' c' = N''.N (τ a') (τ b') (τ c')) (P : FSymbols R N) :
    (P.reindex σ hu₁ hN₁).reindex τ hu₂ hN₂ =
      P.reindex (σ.trans τ) (by simp [hu₁, hu₂]) (by simp [hN₁, hN₂]) := by
  ext a'' b'' c'' d'' ⟨e'', i'', j''⟩ ⟨f'', k'', l''⟩
  simp only [reindex_F_apply, leftSymmEquiv_apply, rightSymmEquiv_apply]
  exact F_cast_of_eq P rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem reindex_trans (σ : ι ≃ ι') (τ : ι' ≃ ι'') (hu₁ : σ N.unit = N'.unit)
    (hN₁ : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) (hu₂ : τ N'.unit = N''.unit)
    (hN₂ : ∀ a' b' c', N'.N a' b' c' = N''.N (τ a') (τ b') (τ c'))
    (hu₁₂ : (σ.trans τ) N.unit = N''.unit)
    (hN₁₂ : ∀ a b c, N.N a b c = N''.N ((σ.trans τ) a) ((σ.trans τ) b) ((σ.trans τ) c)) :
    (FSymbols.reindex (σ.trans τ) hu₁₂ hN₁₂ : FSymbols R N → FSymbols R N'') =
      FSymbols.reindex τ hu₂ hN₂ ∘ FSymbols.reindex σ hu₁ hN₁ :=
  funext fun P ↦ (reindex_trans_apply σ τ hu₁ hN₁ hu₂ hN₂ P).symm

/-- `FSymbols.reindex` along a unit- and multiplicity-preserving bijection as an equivalence. -/
def reindexEquiv (σ : ι ≃ ι') (hu : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) : FSymbols R N ≃ FSymbols R N' where
  toFun := reindex σ hu hN
  invFun := reindex σ.symm (by rw [← hu, σ.symm_apply_apply]) (N_eq_N_symm σ hN)
  left_inv _ := by simp
  right_inv _ := by simp

@[simp] theorem reindexEquiv_apply (σ : ι ≃ ι') (hu : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) (P : FSymbols R N) :
    reindexEquiv σ hu hN P = P.reindex σ hu hN := (rfl)

@[simp] theorem reindexEquiv_symm_apply (σ : ι ≃ ι') (hu : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) (P' : FSymbols R N') :
    (reindexEquiv σ hu hN).symm P' =
      P'.reindex σ.symm (by rw [← hu, σ.symm_apply_apply]) (N_eq_N_symm σ hN) := (rfl)

/-- Base change of `FSymbols` along a ring homomorphism `f : R →+* S`, applying `f` entrywise to
`F` and `Finv`. -/
def map (f : R →+* S) (P : FSymbols R N) : FSymbols S N where
  F a b c d := (P.F a b c d).map f
  Finv a b c d := (P.Finv a b c d).map f
  F_mul_Finv _ _ _ _ := by
    rw [← Matrix.map_mul, P.F_mul_Finv, Matrix.map_one f (map_zero f) (map_one f)]
  Finv_mul_F _ _ _ _ := by
    rw [← Matrix.map_mul, P.Finv_mul_F, Matrix.map_one f (map_zero f) (map_one f)]
  pentagon A B C D E p q r s i₁ i₂ i₃ k m n := by
    simpa [Matrix.map_apply, map_sum, map_mul] using
      congrArg f (P.pentagon A B C D E p q r s i₁ i₂ i₃ k m n)
  triangle _ _ _ _ _ := by split_ifs with h <;> simp [P.triangle, h]

@[simp] theorem map_F_apply (f : R →+* S) (P : FSymbols R N) (a b c d : ι) (x : N.Left a b c d)
    (y : N.Right a b c d) : (P.map f).F a b c d x y = f (P.F a b c d x y) := (rfl)
@[simp] theorem map_Finv_apply (f : R →+* S) (P : FSymbols R N) (a b c d : ι) (y : N.Right a b c d)
    (x : N.Left a b c d) : (P.map f).Finv a b c d y x = f (P.Finv a b c d y x) := (rfl)
theorem map_F (f : R →+* S) (P : FSymbols R N) (a b c d : ι) :
    (P.map f).F a b c d = (P.F a b c d).map f := (rfl)
theorem map_Finv (f : R →+* S) (P : FSymbols R N) (a b c d : ι) :
    (P.map f).Finv a b c d = (P.Finv a b c d).map f := (rfl)

@[simp] theorem map_id_apply (P : FSymbols R N) : P.map (RingHom.id R) = P := by ext; simp
theorem map_id : (FSymbols.map (RingHom.id R) : FSymbols R N → FSymbols R N) = id :=
  funext map_id_apply

@[simp] theorem map_comp_apply (f : R →+* S) (g : S →+* T) (P : FSymbols R N) :
    (P.map f).map g = P.map (g.comp f) := by ext; simp
theorem map_comp (f : R →+* S) (g : S →+* T) :
    (FSymbols.map (g.comp f) : FSymbols R N → FSymbols T N) = FSymbols.map g ∘ FSymbols.map f :=
  funext fun P ↦ (map_comp_apply f g P).symm

/-- Base change of `FSymbols` along a ring isomorphism `e : R ≃+* S` as an equivalence. -/
def mapRingEquiv (e : R ≃+* S) : FSymbols R N ≃ FSymbols S N where
  toFun := map (e : R →+* S)
  invFun := map (e.symm : S →+* R)
  left_inv _ := by simp
  right_inv _ := by simp

@[simp] theorem mapRingEquiv_apply (e : R ≃+* S) (P : FSymbols R N) :
    mapRingEquiv e P = P.map (e : R →+* S) := (rfl)
@[simp] theorem mapRingEquiv_symm (e : R ≃+* S) :
    (mapRingEquiv e : FSymbols R N ≃ FSymbols S N).symm = mapRingEquiv e.symm := (rfl)

/-- `FSymbols.reindex` and `FSymbols.map` commute. -/
theorem reindex_map_apply (f : R →+* S) (σ : ι ≃ ι') (hu : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) (P : FSymbols R N) :
    (P.map f).reindex σ hu hN = (P.reindex σ hu hN).map f := by ext; simp

theorem reindex_comp_map (f : R →+* S) (σ : ι ≃ ι') (hu : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) :
    (FSymbols.reindex σ hu hN ∘ FSymbols.map f : FSymbols R N → FSymbols S N') =
      FSymbols.map f ∘ FSymbols.reindex σ hu hN := funext (reindex_map_apply f σ hu hN)

end ReindexAndMap

end FSymbols

/-! ### Relabeling and base change for R-symbols -/

namespace RSymbols

section ReindexAndMap

open FusionRules (N_eq_N_symm)

variable {K : Type v} {L : Type v'} {M : Type v''} [CommRing K] [CommRing L] [CommRing M]
  {ι : Type u} {ι' : Type u'} {ι'' : Type u''}
  [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype ι''] [DecidableEq ι'']
  {N : FusionRules ι} {N' : FusionRules ι'} {N'' : FusionRules ι''}

private theorem R_cast_of_eq {P : FSymbols K N} (Q : RSymbols P) {a₁ a b₁ b c₁ c : ι}
    (ha : a₁ = a) (hb : b₁ = b) (hc : c₁ = c)
    {i₁ : Fin (N.N a₁ b₁ c₁)} {i : Fin (N.N a b c)} (hi : i₁.val = i.val)
    {j₁ : Fin (N.N b₁ a₁ c₁)} {j : Fin (N.N b a c)} (hj : j₁.val = j.val) :
    Q.R a₁ b₁ c₁ i₁ j₁ = Q.R a b c i j := by
  subst ha; subst hb; subst hc; rw [Fin.ext hi, Fin.ext hj]

/-- Transport `RSymbols` covariantly along a unit- and multiplicity-preserving bijection
`σ : ι ≃ ι'`. -/
def reindex (σ : ι ≃ ι') (hu : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) {P : FSymbols K N}
    (Q : RSymbols P) : RSymbols (P.reindex σ hu hN) where
  R a' b' c' := (Q.R (σ.symm a') (σ.symm b') (σ.symm c')).submatrix
    (finCongr (N_eq_N_symm σ hN a' b' c')) (finCongr (N_eq_N_symm σ hN b' a' c'))
  Rinv a' b' c' := (Q.Rinv (σ.symm a') (σ.symm b') (σ.symm c')).submatrix
    (finCongr (N_eq_N_symm σ hN b' a' c')) (finCongr (N_eq_N_symm σ hN a' b' c'))
  R_mul_Rinv _ _ _ := by rw [Matrix.submatrix_mul_equiv, Q.R_mul_Rinv, Matrix.submatrix_one_equiv]
  Rinv_mul_R _ _ _ := by rw [Matrix.submatrix_mul_equiv, Q.Rinv_mul_R, Matrix.submatrix_one_equiv]
  hexagon_forward a' b' c' d' e' g' i' j' n' o' := by
    refine Eq.trans ?_ ((Q.hexagon_forward
      (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d') (σ.symm e') (σ.symm g')
      (i'.cast (N_eq_N_symm σ hN a' b' e')) (j'.cast (N_eq_N_symm σ hN e' c' d'))
      (n'.cast (N_eq_N_symm σ hN c' a' g')) (o'.cast (N_eq_N_symm σ hN b' g' d'))).trans
        (Eq.symm ?_))
    · exact Fintype.sum_equiv σ.symm _ _ fun f' ↦
        Fintype.sum_equiv (finCongr (N_eq_N_symm σ hN b' c' f')) _ _ fun _ ↦
          Fintype.sum_equiv (finCongr (N_eq_N_symm σ hN a' f' d')) _ _ fun _ ↦
            Fintype.sum_equiv (finCongr (N_eq_N_symm σ hN f' a' d')) _ _ fun _ ↦ by simp
    · exact Fintype.sum_equiv (finCongr (N_eq_N_symm σ hN b' a' e')) _ _ fun _ ↦
        Fintype.sum_equiv (finCongr (N_eq_N_symm σ hN a' c' g')) _ _ fun _ ↦ by simp
  hexagon_reverse a' b' c' d' f' g' k' l' n' o' := by
    refine Eq.trans ?_ ((Q.hexagon_reverse
      (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d') (σ.symm f') (σ.symm g')
      (k'.cast (N_eq_N_symm σ hN b' c' f')) (l'.cast (N_eq_N_symm σ hN a' f' d'))
      (n'.cast (N_eq_N_symm σ hN c' a' g')) (o'.cast (N_eq_N_symm σ hN g' b' d'))).trans
        (Eq.symm ?_))
    · exact Fintype.sum_equiv σ.symm _ _ fun e' ↦
        Fintype.sum_equiv (finCongr (N_eq_N_symm σ hN a' b' e')) _ _ fun _ ↦
          Fintype.sum_equiv (finCongr (N_eq_N_symm σ hN e' c' d')) _ _ fun _ ↦
            Fintype.sum_equiv (finCongr (N_eq_N_symm σ hN c' e' d')) _ _ fun _ ↦ by simp
    · exact Fintype.sum_equiv (finCongr (N_eq_N_symm σ hN c' b' f')) _ _ fun _ ↦
        Fintype.sum_equiv (finCongr (N_eq_N_symm σ hN a' c' g')) _ _ fun _ ↦ by simp

section ReindexLemmas

variable (σ : ι ≃ ι') (hu : σ N.unit = N'.unit) (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c))

@[simp] theorem reindex_R_apply {P : FSymbols K N} (Q : RSymbols P) (a' b' c' : ι')
    (i' : Fin (N'.N a' b' c')) (j' : Fin (N'.N b' a' c')) :
    (Q.reindex σ hu hN).R a' b' c' i' j' = Q.R (σ.symm a') (σ.symm b') (σ.symm c')
      (i'.cast (N_eq_N_symm σ hN a' b' c')) (j'.cast (N_eq_N_symm σ hN b' a' c')) := by
  simp [reindex]

@[simp] theorem reindex_Rinv_apply {P : FSymbols K N} (Q : RSymbols P) (a' b' c' : ι')
    (j' : Fin (N'.N b' a' c')) (i' : Fin (N'.N a' b' c')) :
    (Q.reindex σ hu hN).Rinv a' b' c' j' i' = Q.Rinv (σ.symm a') (σ.symm b') (σ.symm c')
      (j'.cast (N_eq_N_symm σ hN b' a' c')) (i'.cast (N_eq_N_symm σ hN a' b' c')) := by
  simp [reindex]

theorem reindex_R {P : FSymbols K N} (Q : RSymbols P) (a' b' c' : ι') :
    (Q.reindex σ hu hN).R a' b' c' = (Q.R (σ.symm a') (σ.symm b') (σ.symm c')).submatrix
      (finCongr (N_eq_N_symm σ hN a' b' c')) (finCongr (N_eq_N_symm σ hN b' a' c')) := (rfl)

theorem reindex_Rinv {P : FSymbols K N} (Q : RSymbols P) (a' b' c' : ι') :
    (Q.reindex σ hu hN).Rinv a' b' c' = (Q.Rinv (σ.symm a') (σ.symm b') (σ.symm c')).submatrix
      (finCongr (N_eq_N_symm σ hN b' a' c')) (finCongr (N_eq_N_symm σ hN a' b' c')) := (rfl)

end ReindexLemmas

@[simp] theorem reindex_cast {P₁ P₂ : FSymbols K N} (h : P₁ = P₂) (Q : RSymbols P₁) (σ : ι ≃ ι')
    (hu : σ N.unit = N'.unit) (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) :
    (Q.cast h).reindex σ hu hN =
      (Q.reindex σ hu hN).cast (congrArg (FSymbols.reindex σ hu hN) h) := by ext; simp

@[simp] theorem cast_reindex_refl (hu : Equiv.refl ι N.unit = N.unit)
    (hN : ∀ a b c, N.N a b c = N.N (Equiv.refl ι a) (Equiv.refl ι b) (Equiv.refl ι c))
    {P : FSymbols K N} (Q : RSymbols P)
    (h : P.reindex (Equiv.refl ι) hu hN = P := FSymbols.reindex_refl_apply hu hN P) :
    (Q.reindex (Equiv.refl ι) hu hN).cast h = Q := by
  ext a b c i j; rw [cast_R_apply, reindex_R_apply]; exact R_cast_of_eq Q rfl rfl rfl rfl rfl

@[simp] theorem cast_reindex_trans (σ : ι ≃ ι') (τ : ι' ≃ ι'') (hu₁ : σ N.unit = N'.unit)
    (hN₁ : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) (hu₂ : τ N'.unit = N''.unit)
    (hN₂ : ∀ a' b' c', N'.N a' b' c' = N''.N (τ a') (τ b') (τ c')) {P : FSymbols K N}
    (Q : RSymbols P) (h : (P.reindex σ hu₁ hN₁).reindex τ hu₂ hN₂ =
      P.reindex (σ.trans τ) (by simp [hu₁, hu₂]) (by simp [hN₁, hN₂]) :=
      FSymbols.reindex_trans_apply σ τ hu₁ hN₁ hu₂ hN₂ P) :
    ((Q.reindex σ hu₁ hN₁).reindex τ hu₂ hN₂).cast h =
      Q.reindex (σ.trans τ) (by simp [hu₁, hu₂]) (by simp [hN₁, hN₂]) := by
  ext a'' b'' c'' i'' j''; simp only [cast_R_apply, reindex_R_apply]
  exact R_cast_of_eq Q rfl rfl rfl rfl rfl

@[simp] theorem cast_reindex_reindex_symm (σ : ι ≃ ι') (hu : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) (hu' : σ.symm N'.unit = N.unit)
    (hN' : ∀ a' b' c', N'.N a' b' c' = N.N (σ.symm a') (σ.symm b') (σ.symm c'))
    {P : FSymbols K N} (Q : RSymbols P) (h : (P.reindex σ hu hN).reindex σ.symm hu' hN' = P) :
    ((Q.reindex σ hu hN).reindex σ.symm hu' hN').cast h = Q := by
  ext a b c i j; simp only [cast_R_apply, reindex_R_apply]
  exact R_cast_of_eq Q (σ.symm_apply_apply a) (σ.symm_apply_apply b) (σ.symm_apply_apply c) rfl rfl

@[simp] theorem cast_reindex_symm_reindex (σ : ι ≃ ι') (hu' : σ.symm N'.unit = N.unit)
    (hN' : ∀ a' b' c', N'.N a' b' c' = N.N (σ.symm a') (σ.symm b') (σ.symm c'))
    (hu : σ N.unit = N'.unit) (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c))
    {P' : FSymbols K N'} (Q' : RSymbols P')
    (h : (P'.reindex σ.symm hu' hN').reindex σ hu hN = P') :
    ((Q'.reindex σ.symm hu' hN').reindex σ hu hN).cast h = Q' :=
  cast_reindex_reindex_symm σ.symm hu' hN' hu hN Q' h

/-- `RSymbols.reindex` along a unit- and multiplicity-preserving bijection as an equivalence. -/
def reindexEquiv (σ : ι ≃ ι') (hu : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) (P : FSymbols K N) :
    RSymbols P ≃ RSymbols (P.reindex σ hu hN) where
  toFun := reindex σ hu hN
  invFun Q' :=
    (Q'.reindex σ.symm (by rw [← hu, σ.symm_apply_apply]) (N_eq_N_symm σ hN)).cast (by simp)
  left_inv _ := by simp
  right_inv _ := by simp

@[simp] theorem reindexEquiv_apply (σ : ι ≃ ι') (hu : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) (P : FSymbols K N) (Q : RSymbols P) :
    reindexEquiv σ hu hN P Q = Q.reindex σ hu hN := (rfl)
@[simp] theorem reindexEquiv_symm_apply (σ : ι ≃ ι') (hu : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) (P : FSymbols K N)
    (Q' : RSymbols (P.reindex σ hu hN)) : (reindexEquiv σ hu hN P).symm Q' =
      (Q'.reindex σ.symm (by rw [← hu, σ.symm_apply_apply]) (N_eq_N_symm σ hN)).cast (by simp) :=
  (rfl)

/-- Base change of `RSymbols` along a ring homomorphism `f : K →+* L`, applying `f` entrywise to
`R` and `Rinv`. -/
def map (f : K →+* L) {P : FSymbols K N} (Q : RSymbols P) : RSymbols (P.map f) where
  R a b c := (Q.R a b c).map f
  Rinv a b c := (Q.Rinv a b c).map f
  R_mul_Rinv _ _ _ := by
    rw [← Matrix.map_mul, Q.R_mul_Rinv, Matrix.map_one f (map_zero f) (map_one f)]
  Rinv_mul_R _ _ _ := by
    rw [← Matrix.map_mul, Q.Rinv_mul_R, Matrix.map_one f (map_zero f) (map_one f)]
  hexagon_forward a b c d e g i j n o := by
    simpa [Matrix.map_apply, map_sum, map_mul] using
      congrArg f (Q.hexagon_forward a b c d e g i j n o)
  hexagon_reverse a b c d e g k l n o := by
    simpa [Matrix.map_apply, map_sum, map_mul] using
      congrArg f (Q.hexagon_reverse a b c d e g k l n o)

@[simp] theorem map_R_apply (f : K →+* L) {P : FSymbols K N} (Q : RSymbols P) (a b c : ι)
    (i : Fin (N.N a b c)) (j : Fin (N.N b a c)) :
    (Q.map f).R a b c i j = f (Q.R a b c i j) := (rfl)
@[simp] theorem map_Rinv_apply (f : K →+* L) {P : FSymbols K N} (Q : RSymbols P) (a b c : ι)
    (j : Fin (N.N b a c)) (i : Fin (N.N a b c)) :
    (Q.map f).Rinv a b c j i = f (Q.Rinv a b c j i) := (rfl)
theorem map_R (f : K →+* L) {P : FSymbols K N} (Q : RSymbols P) (a b c : ι) :
    (Q.map f).R a b c = (Q.R a b c).map f := (rfl)
theorem map_Rinv (f : K →+* L) {P : FSymbols K N} (Q : RSymbols P) (a b c : ι) :
    (Q.map f).Rinv a b c = (Q.Rinv a b c).map f := (rfl)

@[simp] theorem map_cast {P₁ P₂ : FSymbols K N} (h : P₁ = P₂) (Q : RSymbols P₁) (f : K →+* L) :
    (Q.cast h).map f = (Q.map f).cast (congrArg (FSymbols.map f) h) := by ext; simp
@[simp] theorem cast_map_id {P : FSymbols K N} (Q : RSymbols P)
    (h : P.map (RingHom.id K) = P := FSymbols.map_id_apply P) :
    (Q.map (RingHom.id K)).cast h = Q := by ext; simp
@[simp] theorem cast_map_comp (f : K →+* L) (g : L →+* M) {P : FSymbols K N} (Q : RSymbols P)
    (h : (P.map f).map g = P.map (g.comp f) := FSymbols.map_comp_apply f g P) :
    ((Q.map f).map g).cast h = Q.map (g.comp f) := by ext; simp

@[simp] theorem cast_map_map_symm (e : K ≃+* L) {P : FSymbols K N} (Q : RSymbols P)
    (h : (P.map (e : K →+* L)).map (e.symm : L →+* K) = P) :
    ((Q.map (e : K →+* L)).map (e.symm : L →+* K)).cast h = Q := by
  ext a b c i j; rw [cast_R_apply, map_R_apply, map_R_apply]; simp
@[simp] theorem cast_map_symm_map (e : K ≃+* L) {P' : FSymbols L N} (Q' : RSymbols P')
    (h : (P'.map (e.symm : L →+* K)).map (e : K →+* L) = P') :
    ((Q'.map (e.symm : L →+* K)).map (e : K →+* L)).cast h = Q' := cast_map_map_symm e.symm Q' h

/-- Base change of `RSymbols` along a ring isomorphism `e : K ≃+* L` as an equivalence. -/
def mapRingEquiv (e : K ≃+* L) (P : FSymbols K N) :
    RSymbols P ≃ RSymbols (P.map (e : K →+* L)) where
  toFun := map (e : K →+* L)
  invFun Q' := (Q'.map (e.symm : L →+* K)).cast (by simp)
  left_inv _ := by simp
  right_inv _ := by simp

@[simp] theorem mapRingEquiv_apply (e : K ≃+* L) (P : FSymbols K N) (Q : RSymbols P) :
    mapRingEquiv e P Q = Q.map (e : K →+* L) := (rfl)
@[simp] theorem mapRingEquiv_symm_apply (e : K ≃+* L) (P : FSymbols K N)
    (Q' : RSymbols (P.map (e : K →+* L))) :
    (mapRingEquiv e P).symm Q' = (Q'.map (e.symm : L →+* K)).cast (by simp) := (rfl)

/-- `RSymbols.reindex` and `RSymbols.map` commute up to `RSymbols.cast` along
`FSymbols.reindex_map_apply`. -/
theorem cast_reindex_map (f : K →+* L) (σ : ι ≃ ι') (hu : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) {P : FSymbols K N} (Q : RSymbols P)
    (h : (P.map f).reindex σ hu hN = (P.reindex σ hu hN).map f :=
      FSymbols.reindex_map_apply f σ hu hN P) :
    ((Q.map f).reindex σ hu hN).cast h = (Q.reindex σ hu hN).map f := by ext; simp

end ReindexAndMap

end RSymbols

end TauCeti
