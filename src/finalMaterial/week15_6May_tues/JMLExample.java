package week15_6May_tues;

public class JMLExample {
    //function contract
    /*@
        requires y >= 0;
        ensures \result == x*y;
    */
    public static int mult(int x, int y) {
        //what should we do here?
        //throw an exception if our precondition isn't met
        if (y < 0) {
            throw new IllegalArgumentException("second parameter must be nonnegative");
        }

        int sum = 0;
        int count = 0;

        while (count < y) {
            sum = sum + x;
            count = count + 1;
        }

        //what should we do here?
        //assert our postcondition

        assert sum == x*y;

        return sum;
    }

    //function contract
    /*@

    */
    public static void changeArray(int[] nums) {
        //what should we do here?

        //save "old" version of nums
        int[] oldElem = new int[nums.length];
        System.arraycopy(nums, 0, oldElem, 0, nums.length);

        int temp = nums[0];
        nums[0] = nums[nums.length-1];
        nums[nums.length-1] = temp;

        //what should we do here?
    }
}
