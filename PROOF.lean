import tactic                         -- import Lean's tactics
import data.real.basic                -- import the real numbers
import topology.metric_space.basic    -- imports Lean metric space structure
import analysis.normed_space.basic
import analysis.inner_product_space.basic
import analysis.special_functions.pow
import data.real.sqrt
import order.complete_lattice
import data.nat.basic
import section02reals.ProjectOneFinal_Muhammed

/- We begin by defining E to be a (complete) inner product space, i.e. a vector space with an inner product -/
variables {E : Type} [inner_product_space ℝ E] [complete_space E]
variables {ι : Type}
/-------------------------------------------------------------------------------------------------
SECTION 1 : IN PREPARATION FOR THE HILBERT PROJECTION THEOREM              

In this section we provide pre-requisite definitions which we will need for our final boss:
          *THE HILBERT PROJECTION THEOREM* 
-------------------------------------------------------------------------------------------------/

/- Section 1 : Preliminary definitions  -/

-- Cauchy sequence in our normed space
def is_cauchy (y : ℕ → E) : Prop :=
∀ (ε > 0), ∃ (N : ℕ), ∀ m ≥ N, ∀ n ≥ N, ∥y n - y m∥ < ε

-- Convergence of real numbers
/-def tendsto (y : ℕ → ℝ) (x : ℝ) : Prop :=
∀ (ε > 0), ∃ B : ℕ, ∀ n, B ≤ n → |(y n) - x| < ε -/

-- Convergence in our normed space
def tendstoN (y : ℕ → E) (x : E) : Prop :=
∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → ∥(y n) - x∥ < ε

-- Linear Subspace of E
def is_linear_subspace (L : set E) : Prop :=
(∀ (a b : ℝ), ∀ (x y ∈ L), ( (a • x) + (b • y) ) ∈ L) ∧ ((0 : E) ∈ L)

-- Closed subset of E
def is_closedN (C : set E) : Prop :=
∀ (y : ℕ → E), (∀ (n : ℕ), y n ∈ C) → (∀ (x : E), tendstoN y x ↔ x ∈ C)

-- The following definition of closedness is also applicable since our space E is complete
def is_closedN_equiv (C : set E) : Prop :=
∀ (y : ℕ → E), (∀ (n : ℕ), y n ∈ C) → is_cauchy y → (∃ x ∈ C , tendstoN y x)  

-- Convex subset
def is_convex (C : set E) : Prop :=
∀ (x y : E), ∀ (t : ℝ), ((0 : ℝ) < t ∧ t < (1 : ℝ)) → ((1-t)•x + t•y) ∈ C

/-------------------------------------------------------------------------------------------------
SECTION 2 : PRELIMINARY LEMMAS             

In this section we provide the pre-requisite lemmas which we will need.
-------------------------------------------------------------------------------------------------/

-- A simple rule for inequalities which we will use later
lemma le_trans_proj {a b c d e s : ℝ} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : -s ≤ e) : 
                    2 * a + 2 * c - s ≤ 2 * b + 2 * d + e :=
begin
  refine add_le_add _ h3,
  rw ← left_distrib, rw ← left_distrib, simp,
  exact add_le_add h1 h2,
end

-- Properties of cauchy sequences
lemma cauchy_in_closed (L : set E) (h1 : is_closedN L) (h1a : is_closedN_equiv L) (y : ℕ → E) (h2 : is_cauchy y) (h3 : ∀ (n : ℕ), y n ∈ L) :
∃ (t ∈ L), tendstoN y t :=
begin
  rw is_closedN at h1,
  specialize h1 y h3,
  rw is_closedN_equiv at h1a,
  specialize h1a y h3 h2,
  cases h1a with x h1a,
  cases h1a with Hx h1a,
  use x, split, exact Hx,
  exact h1a,
end

-- Algebra of limits: addition
theorem tendsto_add' {a b : ℕ → ℝ} {t u : ℝ}
  (ha : tendsto a t) (hb : tendsto b u) :
  tendsto (λ n, a n + b n) (t + u) :=
begin
  sorry,
end

-- Lower bound property
lemma LB_proj (a b : ℝ) : (∀ (ε > 0), a < b + ε) → a ≤ b :=
begin
  by_contra,
  simp at h,
  cases h with h1 h2,
  specialize h1 ((a-b)/2 : ℝ) _,
  rotate,
  ring_nf at h1,
  have h3 : a < (1/2 : ℝ) * a + (1/2 : ℝ) * a,
    refine gt.lt _, linarith, 
  ring_nf at h3, 
  have h3' : a < a → false := has_lt.lt.false,
  apply h3', exact h3,
  linarith,
end

-- Algebra of inner products (i)
lemma eq_one_proj (c : ℕ → E) (x : E) : 
∀ (n m : ℕ), ∥c n - c m∥^2 = ∥c n - x∥^2 + ∥c m - x∥^2 - 2 * (inner (c n - x) (c m - x) : ℝ) :=
begin
  intros n m,             -- let n m be two naturals
  have C1_1 : ∀ (x y : E), ∥x-y∥^2 = ∥x∥^2 + ∥y∥^2 - 2 * (inner x y : ℝ),
   {intros x y,
    convert norm_sub_pow_two_real using 1,
    ring_nf},
    specialize C1_1 (c n - x) (c m - x),
    ring_nf at C1_1 ⊢,
    simp at C1_1, exact C1_1,
end

-- Algebra of inner products (ii) 
lemma eq_two_proj (c : ℕ → E) (x : E) : 
∀ (n m : ℕ), 4 * ∥ (1/2 : ℝ)•(c n + c m) - x ∥^ 2 = ∥c n - x∥^(2) + ∥c m - x∥^2 + 2 * (inner (c n - x) (c m - x) : ℝ) :=
begin
  intros n m,
  have C2_1 : 4 * ∥(1 / 2 : ℝ) • (c n + c m) - x∥^(2) = ∥c n + c m - (2 : ℝ)•x∥ ^ 2,
    have C2_2 : ∀ (a : ℝ), a ≥ 0 → ∀ (x : E), a * ∥x∥ ^ 2 = ∥ real.sqrt(a) • x∥ ^ 2,
      {intros a ha x,
       rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, real_inner_smul_left, real_inner_smul_right, ← mul_assoc],
       ring_nf,
       rw real.sq_sqrt,
       ring_nf, exact ha},
    specialize C2_2 4 _, linarith,
    specialize C2_2 ((1 / 2 : ℝ) • (c n + c m) - x),
    have C2_3 : real.sqrt 4 • ((1 / 2 : ℝ) • (c n + c m) - x) = c n + c m - (2 : ℝ) • x,
      {have C2_4 : real.sqrt 4 = 2, 
        {rw real.sqrt_eq_iff_mul_self_eq; linarith},
          rw C2_4, rw smul_add, 
          rw smul_sub, rw smul_add,
          rw ← smul_assoc, rw ← smul_assoc,
          rw smul_eq_mul, simp},
    rw C2_3 at C2_2,
    exact C2_2,
    rw C2_1,
    have C2_5 : ∀ (x y : E), ∥x+y∥^2 = ∥x∥^2 + ∥y∥^2 + 2 * (inner x y : ℝ),
      {intros x y,
       convert norm_add_pow_two_real using 1,
       ring_nf},
    specialize C2_5 (c n - x) (c m - x),
    have C2_6 : c n - x + (c m - x) = c n + c m - (2 : ℝ) •x,
      {rw ← add_sub_assoc,
       rw add_comm, rw ← add_sub_assoc,
       rw add_comm, ring_nf,
      have C2_7 : - x - x = - (2 : ℝ) • x,
        {rw [(by norm_cast : (-2 : ℝ) = (-2 : ℤ)), ← zsmul_eq_smul_cast],
         abel,},
      rw [(by norm_cast : (2 : ℝ) = (2 : ℤ)), ← zsmul_eq_smul_cast],
         abel,
      },
    rw C2_6 at C2_5,
    exact C2_5,
end

-- Property (i) of L being a closed subspace
lemma LB_inf (L : set E) (hL : is_closedN L) (x ζ : E) (hZ : ζ ∈ L) :
(⨅ (i : L), ∥x-i∥) ≤ ∥x-ζ∥ :=
begin
    set δ := ⨅ (i : L), ∥x-i∥ with H, rw H,
    have H0 : ∀ (i : E), 0 ≤ ∥x-i∥,
      {intro i, exact norm_nonneg (x - i)},
    set f := λ i, ∥x-i∥ with F,
    have F' : ∀ (i : L), f i = ∥x-i∥,
      {intro i, rw F},
    have H' :  δ = ⨅ (i : ↥L), f i := rfl,
    have H'' : (⨅ (i : ↥L), ∥x - ↑i∥) = (⨅ (i : ↥L), f i) := rfl,

    rw H'',
    lift ζ to L,
    specialize F' ζ,
    rw ← F',

    have hF : bdd_below (set.range f),
      {rw bdd_below,
      rw lower_bounds,
      simp, 
      exact set.nonempty_of_mem H0},

    have P := cinfi_le hF,
    specialize P ζ,
    refine monotone_id _,
    refine cInf_le _ _,
        {rw bdd_below,
         rw lower_bounds,
         simp,
         use 0, simp},
        {simp, use ζ, split, 
         exact hZ, exact F'},
    exact hZ,
end

-- Property (ii) of L being a closed subspace
lemma zero_le_inf (L : set E) (hLN : L ≠ ∅) (hL : is_closedN L) (x : E) :
0 ≤ (⨅ (i : L), ∥x-i∥) :=
begin
  refine monotone_id _,
  refine le_cInf _ _,
    {rw set.range,
     simp, 
     refine set.nonempty.image (λ (a : E), ∥x - a∥) _,
     exact set.nmem_singleton_empty.mp hLN},
  intros b hb,
  rw set.range at hb,
  simp at hb,
  cases hb with y hb,
  cases hb with h1 h2,
  have h2' : 0 ≤ ∥x-y∥ := norm_nonneg (x - y),  
  rwa h2 at h2',
end

-- A well-known inequality for square roots
lemma sqrt_le_add_sqrt (a b : ℝ) (hb : a ≥ 0) (ha : b ≥ 0) : real.sqrt (a+b) ≤ real.sqrt a + real.sqrt b :=
begin
  rw real.sqrt_le_iff, simp at ha hb, split,
    {have UB_2_a : 0 ≤ real.sqrt a := real.sqrt_nonneg a,
     have UB_2_b : 0 ≤ real.sqrt b := real.sqrt_nonneg b,
     have UB_2_c : 0 ≤ real.sqrt a + real.sqrt b := add_nonneg UB_2_a UB_2_b,
     exact UB_2_c},
  
    {rw add_sq, rw real.sq_sqrt, rw real.sq_sqrt, simp, 
     have UB_2_d : 0 ≤ 2 * real.sqrt a, 
        {rw ← div_le_iff', simp, 
         exact real.sqrt_nonneg a, linarith},
     have UB_2_b : 0 ≤ real.sqrt b := real.sqrt_nonneg b,
     exact mul_nonneg UB_2_d UB_2_b, exact ha, exact hb},
end

-- This result gives a sufficient condition for a sequence to be cauchy
lemma bdd_tends_cauchy (c : ℕ → E) (a : ℕ → ℝ) (b : ℕ → ℝ) (ha : tendsto a 0) (hb : tendsto b 0) 
(h :  ∀ (n m ≥ (1 : ℕ)), ∥c n - c m∥ ^ 2 ≤ (a n) + (b m)) : is_cauchy c :=
begin
  rw is_cauchy,
  intros ε hε,
  have hε' : 0 < (1 / 4 : ℝ) * ε^2 := by nlinarith,
  rw tendsto at ha hb,
  specialize ha ((1 / 4 : ℝ) * ε^2) hε', specialize hb ((1 / 4 : ℝ) * ε^2) hε',
  cases ha with B ha, cases hb with C hb,
  use (max B C + 1),
  /- specialize ha (max B C), specialize hb (max B C),
  specialize ha (le_max_left B C), specialize hb (le_max_right B C), -/
  intros m hm n hn,
  have han : B ≤ n,
    have han' : B ≤ (max B C) + 1,
      have han'' : B ≤ max B C := le_max_left B C,
      exact le_add_right han'',
    exact le_trans han' hn,
  have hbn : C ≤ m,
    have hbn' : C ≤ (max B C) + 1,
      have hbn'' : C ≤ max B C := le_max_right B C,
      exact le_add_right hbn'',
    exact le_trans hbn' hm,
  have zero_le_max : 0 ≤ max B C := zero_le (max B C),
  have HN : 1 ≤ n, exact nat.le_of_add_le_right hn,
  have HM : 1 ≤ m, exact nat.le_of_add_le_right hm,
  specialize ha n han,
  specialize hb m hbn,
  --cases h with N h,
  specialize h n m HN HM,
  have H : (a n + b m) ≤ |a n + b m| := le_abs_self (a n + b m),
  simp at ha hb,
  have H' : |a n + b m| ≤ |a n| + |b m| := abs_add (a n) (b m),
  have H'' : a n + b m ≤ |a n| + |b m| := le_trans H H',
  have H''' : ∥c n - c m∥ ^ 2 ≤ |a n| + |b m| := le_trans h H'',
  rw ← real.sqrt_le_sqrt_iff at H''',       -- square root both sides of H'''
  rotate, {have h1 : 0 ≤ |a n| := abs_nonneg (a n), 
           have h2 : 0 ≤ |b m| := abs_nonneg (b m),
           exact add_nonneg h1 h2},
  rw real.sqrt_sq at H''',
  have G : real.sqrt (|a n| + |b m|) ≤ real.sqrt (|a n|) + real.sqrt (|b m|),
      {have G' := sqrt_le_add_sqrt,
       specialize G' (|a n|) (|b m|) (abs_nonneg (a n)) (abs_nonneg (b m)), exact G'},
  have G' : ∥c n - c m∥ ≤ real.sqrt (|a n|) + real.sqrt (|b m|) := le_trans H''' G,
  rw ← real.sqrt_lt_sqrt_iff at hb ha,
  have four : (4 : ℝ) = (2 : ℝ) ^ 2 := by linarith,
  rw [real.sqrt_mul, real.sqrt_sq, real.sqrt_inv, four, real.sqrt_sq] at hb ha,
  have hc :  real.sqrt (|a n|) + real.sqrt (|b m|) < 2⁻¹ * ε + 2⁻¹ * ε := add_lt_add ha hb,
  ring_nf at hc,
  exact lt_of_le_of_lt G' hc,
  norm_num,         -- proving 0 ≤ 2, a goal left over from applying another theorem previously
  exact le_of_lt hε,
  repeat { norm_num, }, exact le_of_lt hε,
  exact abs_nonneg (b m), exact abs_nonneg (a n),
end

-- Showing that 2/n+1 tends to 0 as n \to \infty
lemma tends_recip : tendsto (λ (n : ℕ), 2 * (1 / (n+1) : ℝ)) 0 :=
begin
  rw tendsto,
  intros ε hε,
  use nat.ceil((2/ε : ℝ)),
  intros n n1, simp,
  have H : ∀ (n : ℕ), |2 * (n + 1 : ℝ)⁻¹| = 2 * (n + 1 : ℝ)⁻¹,
    intro n, rw abs_eq_self, simp, norm_cast, linarith,
  specialize H n, rw H,
  rw mul_inv_lt_iff, rw ← div_lt_iff,
  have n1' :  2 / ε ≤ ↑n, rw nat.ceil_le at n1, exact n1,
  rotate, change 0 < ε at hε, exact hε, norm_cast, exact nat.succ_pos n,
  have n2 : (n : ℝ) < (n : ℝ) + 1 := lt_add_one ↑n,
  exact lt_of_le_of_lt n1' n2,
end

-- The parallelogram law
lemma parallelogram (x y : E) : ∥x + y∥ ^ 2 + ∥x - y∥ ^ 2 = (2 : ℝ) * ∥x∥ ^ 2 + (2 : ℝ) * ∥y∥ ^ 2 :=
begin
  rw [norm_sub_pow_two_real, norm_add_pow_two_real, ← add_assoc, ← add_sub_assoc],
  nlinarith,
end

-- A modified version of the parallelogram law
lemma parallelogram_adjusted (x y : E) : ∥x-y∥^2 = (2 : ℝ)*∥x∥^2 + (2 : ℝ)*∥y∥^2 - (4 : ℝ) * ∥ (1/2 : ℝ) • (x+y)∥^2 :=
begin
  have H := parallelogram x y,
  have h : ∥x+y∥^2 = (4 : ℝ) * ∥ (1/2 : ℝ) • (x+y)∥^2,
    { rw norm_smul,
      simp, have four : (4 : ℝ) = (2 : ℝ) ^ 2 := by linarith,
      rw four, ring_nf},
  rw [← h, eq_sub_iff_add_eq], convert H using 1,
  rw add_comm,
end

theorem exist_sqnce_infi'' (L : set E) (hL : is_closedN L) (hLC : is_linear_subspace L) (hLN : L ≠ ∅) (x : E) (f : L → ℝ) (δ : ℝ) (H : δ = ⨅ (i : ↥L), f i) (hδ : 0 ≤ δ) :
 ∃ (c : ℕ → L), ∀ (n ≥ 1), f (c n) ≤ real.sqrt( δ^2 + (1/n : ℝ) ) :=
begin
  have h :  ∀ (n ≥ 1), (⨅ (i : L), f i) < real.sqrt(δ^2 + (1/n : ℝ) ),
     {intros n n1,
      have D : 0 ≤ δ^2 := sq_nonneg δ,
      have F : 0 ≤ (1/n : ℝ), simp,
      have h1 : (⨅ (i : L), f i)^2 < real.sqrt(δ^2 + (1/n : ℝ) )^2,
        {rw real.sq_sqrt,
         rw ← H, simp, exact nat.succ_le_iff.mp n1, 
         have D : 0 ≤ δ^2 := sq_nonneg δ,
         have F : 0 ≤ (1/n : ℝ), simp, exact add_nonneg D F},
      rw ← real.sqrt_lt_sqrt_iff at h1,
      rw real.sqrt_sq at h1, rw real.sqrt_sq at h1, exact h1,
      have G : 0 ≤ δ^2 + (1/n : ℝ) := add_nonneg D F, exact (δ ^ 2 + 1 / ↑n).sqrt_nonneg,
      rw ← H, exact hδ, rw ← real.sqrt_le_sqrt_iff, rw real.sqrt_zero, rw real.sqrt_sq, rw ← H, exact hδ,
      rw ← H, exact hδ, rw ← H, exact D},      

  have h' : ∀ (a : ℝ), (⨅ (i : L), f i) < real.sqrt(δ^2 + a) → (∃ (x : L), (f x) < real.sqrt(δ^2 + a)),
      intros a h, 
      sorry,
      --exact exists_lt_of_cinfi_lt h,
    
  have h'' : ∀ (n ≥ (1 : ℕ)), ∃ (x : L), (f x) < real.sqrt( δ^2 + (1/n : ℝ) ),
      intros n n1,
      specialize h' (1/n : ℝ), specialize h n n1, specialize h' h, exact h',
    
  have h0 : (0 : E) ∈ L, {rw is_linear_subspace at hLC, cases hLC with hLC1 hLC2, exact hLC2},

  let c : ℕ → L := λ n, @nat.rec (λ _, L) -- in tactic mode so can't use equation compiler :-(
  (⟨0, h0⟩ : L) -- base case
  (λ n l, classical.some (h'' (nat.succ n) (le_add_self))) n, -- other case
  have hc0 : c 0 = (⟨0, h0⟩ : L) := rfl,
  have hcsucc : ∀ d : ℕ, f (c d.succ) < real.sqrt( δ^2 + (1/d.succ : ℝ)) := λ d, classical.some_spec (h'' (nat.succ d) (le_add_self)),
  use c,
  intros n hn, cases n, cases hn, clear hn,
  specialize hcsucc n, exact le_of_lt hcsucc, 
end

theorem exist_sqnce_infi''' (L : set E) (hL : is_closedN L) (hLC : is_linear_subspace L) (hLN : L ≠ ∅) (x : E) (f : L → ℝ) (δ : ℝ) (H : δ = ⨅ (i : ↥L), f i) (hδ : 0 ≤ δ) :
 ∃ (c : ℕ → L), ∀ (n ≥ 1), f (c n) ≤ real.sqrt( δ^2 + (1/n : ℝ) ) :=
begin
  have h :  ∀ (n ≥ 1), (⨅ (i : L), f i) < real.sqrt(δ^2 + (1/n : ℝ) ),
     {intros n n1,
      have D : 0 ≤ δ^2 := sq_nonneg δ,
      have F : 0 ≤ (1/n : ℝ), simp,
      have h1 : (⨅ (i : L), f i)^2 < real.sqrt(δ^2 + (1/n : ℝ) )^2,
        {rw real.sq_sqrt,
         rw ← H, simp, exact nat.succ_le_iff.mp n1, 
         have D : 0 ≤ δ^2 := sq_nonneg δ,
         have F : 0 ≤ (1/n : ℝ), simp, exact add_nonneg D F},
      rw ← real.sqrt_lt_sqrt_iff at h1,
      rw real.sqrt_sq at h1, rw real.sqrt_sq at h1, exact h1,
      have G : 0 ≤ δ^2 + (1/n : ℝ) := add_nonneg D F, exact (δ ^ 2 + 1 / ↑n).sqrt_nonneg,
      rw ← H, exact hδ, rw ← real.sqrt_le_sqrt_iff, rw real.sqrt_zero, rw real.sqrt_sq, rw ← H, exact hδ,
      rw ← H, exact hδ, rw ← H, exact D},      

  have h' : ∀ (a : ℝ), (⨅ (i : L), f i) < real.sqrt(δ^2 + a) → (∃ (x : L), (f x) < real.sqrt(δ^2 + a)),
      intros a h, 
      sorry,
      --exact exists_lt_of_cinfi_lt h,
    
  have h'' : ∀ (n ≥ (1 : ℕ)), ∃ (x : L), (f x) < real.sqrt( δ^2 + (1/n : ℝ) ),
      intros n n1,
      specialize h' (1/n : ℝ), specialize h n n1, specialize h' h, exact h',
    
  have h0 : (0 : E) ∈ L, {rw is_linear_subspace at hLC, cases hLC with hLC1 hLC2, exact hLC2},

  let c : ℕ → L := λ n, @nat.rec (λ _, L) -- in tactic mode so can't use equation compiler :-(
  (⟨0, h0⟩ : L) -- base case
  (λ n l, classical.some (h'' (nat.succ n) (le_add_self))) n, -- other case
  have hc0 : c 0 = (⟨0, h0⟩ : L) := rfl,
  have hcsucc : ∀ d : ℕ, f (c d.succ) < real.sqrt( δ^2 + (1/d.succ : ℝ)) := λ d, classical.some_spec (h'' (nat.succ d) (le_add_self)),
  use c,
  intros n hn, cases n, cases hn, clear hn,
  specialize hcsucc n, exact le_of_lt hcsucc, 
end

/-------------------------------------------------------------------------------------------------
SECTION 3 : THE HILBERT PROJECTION THEOREM              

In this section we prove *THE HILBERT PROJECTION THEOREM* 
-------------------------------------------------------------------------------------------------/

theorem projection (L : set E) (hLN : L ≠ ∅) (hL : is_closedN L) (hL1 : is_closedN_equiv L) (hLL : is_linear_subspace L) (hLC : is_convex L) {z : ι → L} {d : E} :
∀ (x : E), ∃! (y : L), (∥x-y∥ = ⨅ (i : L), ∥x-i∥) :=
begin
  intro x,                               -- let x be a point in our Hilbert space
  set δ := ⨅ (i : L), ∥x-i∥ with H,      -- let δ be the inf (∥x-i∥) over all i ∈ L

  /- let hδ be the proof that 0 ≤ δ ; we will need this later. The proof comes from the lemma
     zero_le_inf which we proved prior to beginning this proof.  -/
  have hδ := zero_le_inf (L) (hLN) (hL) (x), rw ← H at hδ,  

  /- Our first task is to prove the existemce of a sequence (c n) which is contained in L and also
     satisfies ∥x - c n∥^2 ≤ δ^2 + 1/n for any n ∈ ℕ. Call this hypothesis h  -/
  have h : ∃ (c : ℕ → E), ((∀ (n : ℕ), c n ∈ L) ∧ (∀ (n : ℕ), ∥x-c n∥^(2) ≤ δ^2 + ((1/(n+1)) : ℝ))),
    sorry, -- use λ n, (c n).1

  cases h with c hc,      -- Take a sequence which satisfies the above hypothesis, call it c

  cases hc with h1 h2,    
  
/- Goal 1 : Prove that our sequence (c n) is Cauchy -/
  have is_cauchy_c : is_cauchy c,
   {  set a := λ (n : ℕ), 2 * (1 /(n+1) : ℝ) with A, ring_nf at A,
      have A' : ∀ (n : ℕ), a n = 2 * (1/(n+1) : ℝ),
          {intro i,  rw A, simp},
      have B' := A',
      ring_nf at A' B',
     
     have C : ∀ (n m ≥ (1 : ℕ)), ∥c n - c m∥ ^ 2 ≤ (a n) + (a m),
    { intros n m n1 m1,
      specialize A' n, specialize B' m,
      --cases hc with h1 h2,
      rw A', rw B',
       /- First set up equation C1 which says:
        ∀ (n m : ℕ), ∥c n - c m∥ ^ 2 = ∥c n - x∥ ^ 2 + ∥c m - x∥ ^ 2 - 2 * inner (c n - x) (c m - x) -/
      have C1 := eq_one_proj c x,
      /- And now equation C2 which says:
      ∀ (n m : ℕ), 4 * ∥(1 / 2) • (c n + c m) - x∥ ^ 2 
      = ∥c n - x∥ ^ 2 + ∥c m - x∥ ^ 2 + 2 * inner (c n - x) (c m - x)  -/
      have C2 := eq_two_proj c x,

      specialize C1 n m, specialize C2 n m,   -- take m n (already defined naturals) in the above equations
    
    /- To make simplifying the equations much simpler, let's rename the terms in our equations:-/
        set a := ∥c n - c m∥ ^ 2 with T1,
        set b := ∥c n - x∥ ^ 2 + ∥c m - x∥ ^ 2 - 2 * (inner (c n - x) (c m - x) : ℝ) with T2,
        set e := 4 * ∥(1 / 2 : ℝ) • (c n + c m) - x∥ ^ 2 with T3,
        set f := ∥c n - x∥ ^ 2 + ∥c m - x∥ ^ 2 + 2 * (inner (c n - x) (c m - x) : ℝ) with T4,

    /- Adding C1 and C2 together: -/
    have C1_and_C2 : a = b ∧ e = f :=  ⟨C1, C2⟩, 
    rw ← add_eq_add_iff_eq_and_eq at C1_and_C2,

    /- Moving terms around so we can use the lemma eq_sub_of_add_eq to finally subtract the equations-/
    set p := b + f with Y, rw ← Y at C1_and_C2,   -- renaming b + f to p
    have C1_and_C2_sub : a = p - e := eq_sub_of_add_eq (C1_and_C2),  -- subtracting a term from both sides of C1_and_C2    

    /- Now that we've added C1 and C2 together and simplified, let's replace our variables
       a b e f p with their original expressions -/
    rw Y at C1_and_C2_sub, rw T1 at C1_and_C2_sub, rw T2 at C1_and_C2_sub,
    rw T3 at C1_and_C2_sub, rw T4 at C1_and_C2_sub,
    ring_nf at C1_and_C2_sub,

    have h3 := h2,      -- duplicate the hypothesis h2
    specialize h2 n, specialize h3 m,     -- choose N = n and N = m 
    have G := norm_sub_rev, have G' := G,
    specialize G (c n) x, specialize G' (c m) x,
    rw ← G at h2, rw ← G' at h3,


    set ζ := (1 / 2 : ℝ) • (c n + c m) with Z,
    -- We first prove that (c n + c m)/2 ∈ L
    have h4_1 : (1 / 2 : ℝ) • (c n + c m) ∈ L,
        {rw is_convex at hLC,
        specialize hLC (c n) (c m) (1/2 : ℝ), specialize hLC _, split, linarith, linarith,
        ring_nf at hLC, rw ← smul_add at hLC,
        exact hLC},

    have h4 : δ ≤ ∥(1 / 2 : ℝ) • (c n + c m) - x∥,
        {rw norm_sub_rev, rw ← Z at ⊢ h4_1, rw H,
         exact LB_inf (L) (hL) x ζ (h4_1)},
    
    /- Now we can square equation h4 -/
    have h4_sq : δ ^ 2 ≤ ∥(1 / 2 : ℝ) • (c n + c m) - x∥ ^ 2,
      {rw ← abs_of_nonneg hδ at h4,      --  we use the fact |δ| = δ
      rw ← abs_norm_eq_norm at h4,
      exact sq_le_sq h4},
    
    /- Finally we multiply equation h4 by -4 !-/
    have h4_mul : -4 * δ ^ 2 ≥ -4 * ∥(1 / 2 : ℝ) • (c n + c m) - x∥ ^ 2,
      {have neg_4 : (-4 : ℝ) < (0 : ℝ) := by linarith,
       rw ← mul_le_mul_left_of_neg neg_4 at h4_sq, exact h4_sq},

    /- Before we proceed, lets rename the terms in our equations to simple variables to make the
       manipulation less complicated:  -/
    set q := ∥c n - x∥ ^ 2 with T5,
    set r := ∥c m - x∥ ^ 2 with T6,
    set s := 4 * ∥(1 / 2 : ℝ) • (c n + c m) - x∥ ^ 2 with T7, 
    
    /- Rewrite our equations in terms of these new variables: -/
    rw ← T1 at C1_and_C2_sub,
    rw ← T5 at h2, rw ← T6 at h3, 
    ring_nf at h4_mul, rw ← add_sub_assoc at C1_and_C2_sub,
    --ring_nf at T7,

    rw ← T7 at C1_and_C2_sub, rw ← T7 at h4_mul, change -s ≤ -(4 * δ ^ 2) at h4_mul,

    have C3 : a ≤ 2 * (δ ^ 2 + (1/(n+1) : ℝ)) + 2 * (δ ^ 2 + (1/(m+1) : ℝ)) - 4 * δ ^ 2,
      { have C3_est :  2 * q + (2 * r - s) ≤ 2 * (δ^2 + (1/(n+1) : ℝ)) + 2 * (δ^2 + (1/(m+1) : ℝ)) - 4 * δ^2,
            {rw ← add_sub_assoc,
             exact le_trans_proj h2 h3 h4_mul},
        rw ← add_sub_assoc at C3_est,   -- get rid of the brackets in the above expression C3_est
        rw [← T5, ← T6] at C1_and_C2_sub,
        exact eq.trans_le C1_and_C2_sub C3_est},

    ring_nf at C3,
    exact C3,
    cases C1_and_C2 with Ca Cb,
    exact (eq.symm Ca).ge,
    cases C1_and_C2 with Ca Cb,
    exact (eq.symm Cb).ge},
  
  have aT := tends_recip, ring_nf at aT, rw ← A at aT,
  exact bdd_tends_cauchy c a a aT aT C},
 
 /- lemma cauchy_in_closed (L : set E) (h1 : is_closedN L) (h1a : is_closedN_equiv L) (y : ℕ → E) (h2 : is_cauchy y) (h3 : ∀ (n : ℕ), y n ∈ L) :
∃ (t ∈ L), tendstoN y t :=
 -/

 have lim_c : ∃ (y : E) (H : y ∈ L), tendstoN c y,
    exact cauchy_in_closed L hL hL1 c is_cauchy_c h1,
  cases lim_c with ζ lim_c,
  cases lim_c with HC lim_c,
  have ZETA_EQ_DELTA : ∥x-ζ∥ = δ,
  --use ζ, exact HC, simp, split,
  /- Lets show ∥x-ζ∥ ≥ δ -/
  have norm_LB : ∥x-ζ∥ ≥ δ,
    {rw H,
    simp,
    have H0 : ∀ (i : E), 0 ≤ ∥x-i∥,
      {intro i, exact norm_nonneg (x - i)},
    set f := λ i, ∥x-i∥ with F,
    have F' : ∀ (i : L), f i = ∥x-i∥,
      {intro i, rw F},
    have H' :  δ = ⨅ (i : ↥L), f i := rfl,
    have H'' : (⨅ (i : ↥L), ∥x - ↑i∥) = (⨅ (i : ↥L), f i) := rfl,

    rw H'',
    lift ζ to L,
    specialize F' ζ,
    rw ← F',

    have hF : bdd_below (set.range f),
      {rw bdd_below,
      rw lower_bounds,
      simp, 
      exact set.nonempty_of_mem H0},

    have P := cinfi_le hF,
    specialize P ζ,
    refine monotone_id _,
    refine cInf_le _ _,
        {rw bdd_below,
         rw lower_bounds,
         simp,
         use 0, simp},
        {simp, use ζ, split, 
         exact HC, exact F'},
    exact HC},
  
  have norm_UB : ∥x-ζ∥ ≤ δ,
    { /- We are going to tackle this in a somewhat unnatural order: 
         Our first goal is to show real.sqrt (↑n)⁻¹ + ∥c n - ζ∥ tends to 0 as n → ∞.
         The strategy is as follows: 
                      i) prove 1/n → 0 as n → ∞
                      ii) prove ∥c n - ζ∥ → 0 as n → ∞
                      iii) prove the sum of these → 0           -/
        
      set s := λ (n : ℕ), real.sqrt (↑n + 1)⁻¹ with S,    -- label the sequence n → 1/n as s
      set t := λ (n : ℕ), ∥c n - ζ∥ with T,            -- label the sequence n → ∥c n - ζ∥ as t
      -- (i) proving 1/n → 0 as n → ∞ 
      have tends_s : tendsto s 0,
          {sorry},
      -- (ii) proving ∥c n - ζ∥ → 0 as n → ∞ 
      have tends_t : tendsto t 0,
          {sorry},
      -- (iii) prove the sum of these → 0 
      have tends_s_t : tendsto (λ n, s n + t n) 0,
          {have tends_s_t' := tendsto_add' tends_s tends_t,
           simp at tends_s_t', exact tends_s_t'},

      /- Now we need to show ∥x-ζ∥ < δ + ε for any ε >0 using the fact we know 
          s n + t n → 0. Once we have this, we'll be able to conclude ∥x-ζ∥ ≤ δ
          by applyign LB_proj, a lemma proved earlier in preparation for this very step -/

      have UB_5 : ∀ (ε > 0), ∥x-ζ∥ < δ + ε,
        {intros ε hε,
         rw tendsto at tends_s_t,
         specialize tends_s_t ε hε,
         cases tends_s_t with N tB, specialize tB (N+1+1),
         set B := N + 1 + 1 with hB, rw hB at tB,--have tB : 0 ≤ B := zero_le B,
      
      
      have UB_1 : ∥x-ζ∥ ≤ ∥x - c B∥ + ∥c B - ζ∥,
        {have UB_1_a : ∥x-ζ∥ = ∥x + c B - c B - ζ∥ := by simp,
         rw UB_1_a, have UB_1_b := norm_add_le (x - c B) (c B - ζ),
         simp at UB_1_b, rw UB_1_a at UB_1_b, exact UB_1_b},

      -- next square root both sides of ∥x - c n∥ ^ 2 ≤ δ ^ 2 + 1 / ↑n
      specialize h2 B, rw ← real.sqrt_le_sqrt_iff at h2,
      simp at h2,     -- cancelling out the square and square root on the LHS

     -- Before proceeding let's show 0 ≤ δ² and 0 ≤ 1 / B. This will be useful when applying certain results.
      have zδ : 0 ≤ δ^2 := sq_nonneg δ,
      have zn : 0 ≤ (1/B : ℝ), 
          {rw le_div_iff, linarith, rw hB, rw ← nat.succ_eq_add_one, exact nat.cast_pos.2 (N+1).succ_pos},
      
      /- Next we'll need the inequality √(a+b) ≤ √a + √b. This is a lemma we proved earlier
         so let's invoke it here, calling it UB_2  -/
      have UB_2 := sqrt_le_add_sqrt,
      specialize UB_2 (δ ^ 2) (1/(B) : ℝ) zδ zn, 

      ring_nf at UB_2, rw real.sqrt_sq at UB_2,  -- rewrite √δ^2 as δ
      have UB_3 : ∥x - c B∥ ≤ δ + real.sqrt (↑B+1)⁻¹ := le_trans h2 UB_2,
      have UB_4 : ∥x - c B∥ + ∥c B - ζ∥ ≤ δ + real.sqrt ((↑B)⁻¹) + ∥c B - ζ∥,
        {simpa using UB_3,},
        --simp at UB_3 ⊢, exact UB_3}
      have UB_5 : ∥x - ζ∥ ≤ δ + real.sqrt ((↑B)⁻¹) + ∥c B - ζ∥ := le_trans UB_1 UB_4,
      specialize tB (by linarith), simp at tB,

      rw add_assoc at UB_5, 
      have UB_6 : δ + (real.sqrt ((↑B)⁻¹) + ∥c B - ζ∥) ≤ |δ + (real.sqrt ((↑B)⁻¹) + ∥c B - ζ∥)| := le_abs_self (δ + (real.sqrt (↑B)⁻¹ + ∥c B - ζ∥)),
      have UB_7 : |δ + (real.sqrt ((↑B)⁻¹) + ∥c B - ζ∥)| ≤ |δ| + |(real.sqrt ((↑B)⁻¹) + ∥c B - ζ∥)| := abs_add δ (real.sqrt (↑B)⁻¹ + ∥c B - ζ∥),
      have UB_8 : δ + (real.sqrt ((↑B)⁻¹) + ∥c B - ζ∥) ≤ |δ| + |(real.sqrt ((↑B)⁻¹) + ∥c B - ζ∥)| := le_trans UB_6 UB_7,
      have UB_9 : ∥x - ζ∥ ≤ |δ| + |(real.sqrt ((↑B)⁻¹) + ∥c B - ζ∥)| := le_trans UB_5 UB_8,
      /- Now we make note that the terms inside the second modulus are simply our sequences s and t
         so we can express the RHS of our inequality in terms of these sequences -/
      have rS : s B = real.sqrt (↑B)⁻¹ := rfl,
      have tS : t B = ∥c B - ζ∥ := rfl,
      rw ← rS at UB_9, rw ← tS at UB_9, 

      have UB_10 : ∥x - ζ∥ < |δ| + ε,
        { rw ← sub_le_iff_le_add' at UB_9, rw ← sub_lt_iff_lt_add',
          exact lt_of_le_of_lt UB_9 tB},

      convert UB_10 using 1, simp, 
      rw abs_of_nonneg, repeat { exact hδ }, nlinarith}, 
  
    have UB_fin := LB_proj,
    specialize UB_fin (∥x - ζ∥) (δ) UB_5,
    exact UB_fin},

  /- we now have norm_LB: ∥x - ζ∥ ≥ δ and norm_UB: ∥x - ζ∥ ≤ δ,
     and we wish to show  ⊢ ∥x - ζ∥ = δ                   -/
    by_contra, have h' : ∥x-ζ∥ ≠ δ := h,          -- proceed by contradiction
    rw ← has_le.le.lt_iff_ne at h', linarith,     -- using the upper bound to contradict ∥x-ζ∥ ≠ δ
    exact norm_UB,
    use ζ, exact HC, simp, split, exact ZETA_EQ_DELTA,

  intros y hy hy1,
  have H := parallelogram_adjusted (y-x) (ζ-x),
  have H' : (1 / 2 : ℝ) • (y - x + (ζ - x)) = (1 / 2 : ℝ) • (y + ζ) - x,
    rw [← add_sub_assoc, smul_add, smul_sub, smul_add, smul_sub], abel, simp, ring_nf, 
    rw [← smul_assoc, zsmul_eq_mul], simp,
  rw H' at H,

  set T := (1 / 2 : ℝ) • (y + ζ) with Z,
    -- We first prove that (c n + c m)/2 ∈ L
    have h4_1 : (1 / 2 : ℝ) • (y+ζ) ∈ L,
        {rw is_convex at hLC,
        specialize hLC (y) (ζ) (1/2 : ℝ), specialize hLC _, split, linarith, linarith,
        ring_nf at hLC, rw ← smul_add at hLC,
        exact hLC},

    have h4 : δ ≤ ∥(1 / 2 : ℝ) • (y + ζ) - x∥,
        {rw norm_sub_rev, rw ← Z at ⊢ h4_1, rw H,
         exact LB_inf (L) (hL) x T (h4_1)},
    
    /- Now we can square equation h4 -/
    have h4_sq : δ ^ 2 ≤ ∥(1 / 2 : ℝ) • (y + ζ) - x∥ ^ 2,
      {rw ← abs_of_nonneg hδ at h4,      --  we use the fact |δ| = δ
      rw ← abs_norm_eq_norm at h4,
      exact sq_le_sq h4},
    
    /- Finally we multiply equation h4 by -4 !-/
    have h4_mul : - (4 : ℝ) * δ ^ 2 ≥ - (4 : ℝ) * ∥(1 / 2 : ℝ) • (y + ζ) - x∥ ^ 2,
      {have neg_4 : (-4 : ℝ) < (0 : ℝ) := by linarith,
       rw ← mul_le_mul_left_of_neg neg_4 at h4_sq, exact h4_sq},
    rw ← Z at h4_mul, simp at H_1,
    change -(4 : ℝ) * ∥T - x∥ ^ 2 ≤ -(4 : ℝ) * δ ^ 2 at h4_mul,

    have est : ∀ (p ∈ L), δ ≤ ∥p-x∥ ,
      {intro p, rw norm_sub_rev, rw H, exact LB_inf L hL x p},
    have est' := est,
    specialize est ζ HC,
    specialize est' y hy,

    intro J,
    have G := ZETA_EQ_DELTA,
    rw G at H_1, rw norm_sub_rev at hy1, rw hy1 at H_1,
    ring_nf at H_1 h4_mul,
    rw eq_sub_iff_add_eq at H_1,
    rw neg_le_neg_iff at h4_mul,
    have H_2 : ∥y - ζ∥ ^ 2 + (4 : ℝ) * ∥T - x∥ ^ 2 ≤ (4 : ℝ) * ∥T - x∥ ^ 2 := eq.trans_le H_1 h4_mul,
    simp at H_2, rw ← real.sqrt_le_sqrt_iff at H_2, rw [real.sqrt_sq, real.sqrt_zero] at H_2,
    rw norm_le_zero_iff at H_2, rw sub_eq_zero at H_2, exact H_2, exact norm_nonneg (y-ζ), linarith,








end
